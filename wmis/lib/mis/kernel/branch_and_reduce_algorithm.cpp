/******************************************************************************
*****************************************************************************/

#include "branch_and_reduce_algorithm.h"

#include <algorithm>
#include <chrono>
#include <numeric>

#include "graph_extractor.h"
#include "ils/ils.h"
#include "ils/local_search.h"
#include "strongly_connected_components.h"

std::streambuf* cout_handler::cout_rdbuf_backup = std::cout.rdbuf();
std::stringstream cout_handler::buffered_output;
int cout_handler::disable_count = 0;

void branch_and_reduce_algorithm::init_branch_and_reduce_algorithm(bool called_from_fold) {
    if (called_from_fold) {
        global_status.reductions = make_reduction_vector<neighborhood_reduction, fold2_reduction, clique_reduction,
                                                         domination_reduction, twin_reduction>(global_status.n);
    } else if (config.reduction_style == MISConfig::Reduction_Style::DENSE) {
        global_status.reductions =
            make_reduction_vector<neighborhood_reduction, fold2_reduction, clique_reduction, domination_reduction,
                                  twin_reduction, generalized_fold_reduction>(global_status.n);
    } else {
        // MISConfig::Reduction_Style::NORMAL
        global_status.reductions =
            make_reduction_vector<neighborhood_reduction, fold2_reduction, clique_reduction, domination_reduction,
                                  twin_reduction, clique_neighborhood_reduction, critical_set_reduction,
                                  generalized_fold_reduction>(global_status.n);
    }

    global_reduction_map.resize(REDUCTION_NUM);
    for (size_t i = 0; i < global_status.reductions.size(); i++) {
        global_reduction_map[global_status.reductions[i]->get_reduction_type()] = i;
    }

    set_local_reductions = [this, called_from_fold]() {
        if (this->config.reduction_style == MISConfig::Reduction_Style::DENSE) {
            status.reductions =
                make_reduction_vector<neighborhood_reduction, fold2_reduction, clique_reduction, domination_reduction,
                                      twin_reduction, clique_neighborhood_reduction_fast>(status.n);
        } else {
            // MISConfig::Reduction_Style::NORMAL
            if (called_from_fold) {
                status.reductions =
                    make_reduction_vector<neighborhood_reduction, fold2_reduction, clique_reduction,
                                          domination_reduction, twin_reduction, clique_neighborhood_reduction,
                                          critical_set_reduction>(status.n);
            } else {
                status.reductions =
                    make_reduction_vector<neighborhood_reduction, fold2_reduction, clique_reduction,
                                          domination_reduction, twin_reduction, clique_neighborhood_reduction,
                                          critical_set_reduction, generalized_fold_reduction>(status.n);
            }
        }

        local_reduction_map.resize(REDUCTION_NUM);

        for (size_t i = 0; i < status.reductions.size(); i++) {
            local_reduction_map[status.reductions[i]->get_reduction_type()] = i;
        }
    };
}

branch_and_reduce_algorithm::branch_and_reduce_algorithm(graph_access& G, const MISConfig& config,
                                                         bool called_from_fold)
    : config(config),
      global_status(G),
      set_1(global_status.n),
      set_2(global_status.n),
      set_3(global_status.n),
      double_set(global_status.n * 2),
      buffers(2, sized_vector<NodeID>(global_status.n)) {
    init_branch_and_reduce_algorithm(called_from_fold);
}

branch_and_reduce_algorithm::branch_and_reduce_algorithm(graph_access& G, std::vector<IS_status>& node_lower_status,
                                                         NodeWeight is_lower_weight, const MISConfig& config,
                                                         bool called_from_fold)
    : config(config),
      global_status(G, node_lower_status, is_lower_weight),
      set_1(global_status.n),
      set_2(global_status.n),
      set_3(global_status.n),
      double_set(global_status.n * 2),
      buffers(2, sized_vector<NodeID>(global_status.n)),
      local_lower_sol(global_status.n) {
    init_branch_and_reduce_algorithm(called_from_fold);
}

size_t branch_and_reduce_algorithm::deg(NodeID node) const { return status.graph[node].size(); }

void branch_and_reduce_algorithm::set(NodeID node, IS_status mis_status, bool push_modified) {
    status.node_status[node] = mis_status;
    status.remaining_nodes--;
    status.graph.hide_node(node);

    if (push_modified) status.modified_queue.push_back(node);

    if (mis_status == IS_status::included) {
        status.is_weight += status.weights[node];

        for (auto neighbor : status.graph[node]) {
            status.node_status[neighbor] = IS_status::excluded;
            status.remaining_nodes--;
            status.graph.hide_node(neighbor);

            status.modified_queue.push_back(neighbor);
            add_next_level_neighborhood(neighbor);
        }
    } else {
        add_next_level_neighborhood(node);
    }
}

void branch_and_reduce_algorithm::flip_include_exclude(NodeID node) {
    if (status.node_status[node] == IS_status::included) {
        status.node_status[node] = IS_status::excluded;
        status.is_weight -= status.weights[node];

        add_next_level_neighborhood(node);
    } else {
        // node was excluded
        status.node_status[node] = IS_status::included;
        status.is_weight += status.weights[node];

        for (auto neighbor : status.graph[node]) {
            status.node_status[neighbor] = IS_status::excluded;
            status.remaining_nodes--;
            status.graph.hide_node(neighbor);

            status.modified_queue.push_back(neighbor);

            // TODO: try calling "add_next_level_neighborhood" in second loop after this one
            add_next_level_neighborhood(neighbor);
        }
    }
}

void branch_and_reduce_algorithm::unset(NodeID node, bool restore) {
    if (status.node_status[node] == IS_status::included) {
        status.is_weight -= status.weights[node];
    }

    status.node_status[node] = IS_status::not_set;
    status.remaining_nodes++;

    if (restore) status.graph.restore_node(node);
}

void branch_and_reduce_algorithm::fill_global_greedy() {
    auto& nodes = buffers[0];
    nodes.clear();

    for (size_t node = 0; node < global_status.n; node++) {
        if (global_status.node_status[node] == IS_status::not_set) nodes.push_back(node);
    }

    // sort in descending order by node weights
    std::sort(nodes.begin(), nodes.end(),
              [this](NodeID lhs, NodeID rhs) { return global_status.weights[lhs] > global_status.weights[rhs]; });

    for (NodeID node : nodes) {
        bool free_node = true;

        for (NodeID neighbor : global_status.graph[node]) {
            if (global_status.node_status[neighbor] == IS_status::included) {
                free_node = false;
                break;
            }
        }

        if (free_node) {
            global_status.node_status[node] = IS_status::included;
            global_status.is_weight += global_status.weights[node];
        } else {
            global_status.node_status[node] = IS_status::excluded;
        }
    }
}

void branch_and_reduce_algorithm::greedy_initial_is(graph_access& G, sized_vector<NodeID>& tmp_buffer) {
    auto nodes = tmp_buffer;
    nodes.set_size(G.number_of_nodes());

    for (size_t i = 0; i < nodes.size(); i++) {
        nodes[i] = i;
    }

    // sort in descending order by node weights
    std::sort(nodes.begin(), nodes.end(),
              [&](NodeID lhs, NodeID rhs) { return G.getNodeWeight(lhs) > G.getNodeWeight(rhs); });

    for (NodeID node : nodes) {
        bool free_node = true;

        forall_out_edges (G, edge, node) {
            NodeID neighbor = G.getEdgeTarget(edge);
            if (G.getPartitionIndex(neighbor) == 1) {
                free_node = false;
                break;
            }
        }
        endfor

        if (free_node) G.setPartitionIndex(node, 1);
    }
}

void branch_and_reduce_algorithm::compute_ils_pruning_bound() {
    std::cout << "compute_ils_pruning_bound" << std::endl;
    is_ils_best_solution = true;
    cout_handler::disable_cout();

    auto config_cpy = config;
    config_cpy.time_limit = config_cpy.time_limit * status.n / total_ils_node_count / 100;

    best_weight = status.reduction_offset + status.is_weight + run_ils(config_cpy, *local_graph, buffers[0], 1000);

    cout_handler::enable_cout();
    std::cout << (get_current_is_weight() + best_weight) << " [" << t.elapsed() << "]" << std::endl;
}

NodeWeight branch_and_reduce_algorithm::compute_cover_pruning_bound() {
    // Gather remaining nodes
    auto& nodes = buffers[0];
    nodes.clear();

    for (size_t node = 0; node < status.n; node++) {
        if (status.node_status[node] == IS_status::not_set) nodes.emplace_back(node);
    }

    // Sort by descending weight
    // Break ties by degree
    std::sort(nodes.begin(), nodes.end(), [&](NodeID lhs, NodeID rhs) {
        return (status.weights[lhs] > status.weights[rhs] ||
                (status.weights[lhs] == status.weights[rhs] && deg(lhs) > deg(rhs)));
    });

    // Compute node mapping
    NodeID current_node = 0;
    auto& node_mapping = buffers[1];
    node_mapping.set_size(status.n);

    for (NodeID node : nodes) node_mapping[node] = current_node++;

    // Init cliques
    auto& clique = buffers[2];
    auto& clique_weight = buffers[3];
    auto& clique_sizes = buffers[4];
    auto& covered = buffers[5];

    clique.set_size(nodes.size());
    clique_weight.set_size(nodes.size());
    clique_sizes.set_size(nodes.size());
    covered.set_size(nodes.size());

    std::fill(clique_weight.begin(), clique_weight.end(), 0);
    std::fill(clique_sizes.begin(), clique_sizes.end(), 0);
    std::fill(covered.begin(), covered.end(), false);

    for (NodeID node : nodes) clique[node_mapping[node]] = node_mapping[node];

    auto& neigh_clique_sizes = buffers[6];
    neigh_clique_sizes.set_size(nodes.size());

    for (NodeID node : nodes) {
        NodeID v = node_mapping[node];
        // Find heaviest neighboring clique
        NodeID heaviest_clique = v;
        std::fill(neigh_clique_sizes.begin(), neigh_clique_sizes.end(), 0);

        for (NodeID neighbor : status.graph[node]) {
            if (status.node_status[neighbor] == IS_status::not_set) {
                NodeID w = node_mapping[neighbor];

                if (covered[w]) {
                    NodeID c = clique[w];
                    neigh_clique_sizes[c]++;

                    if (neigh_clique_sizes[c] == clique_sizes[c] && clique_weight[c] > clique_weight[heaviest_clique])
                        heaviest_clique = c;
                }
            }
        }

        // Update clique weights/sizes
        clique[v] = heaviest_clique;
        clique_weight[heaviest_clique] = std::max(clique_weight[heaviest_clique], status.weights[node]);
        clique_sizes[heaviest_clique]++;

        // Node is covered
        covered[v] = true;
    }

    // Check clique cover conditions
    // for (NodeID node : nodes) {
    //   NodeID v = node_mapping[node];
    //   NodeID c = clique[v];
    //   NodeID cs = clique_sizes[c];
    //   NodeID num_cn = 1;
    // 	for (NodeID neighbor : status.graph[node]) {
    // 		if (status.node_status[neighbor] == IS_status::not_set) {
    //       NodeID w = node_mapping[neighbor];
    //       if (clique[w] == c) num_cn++;
    //     }
    //   }
    // }

    // Keep unique cliques
    std::sort(clique.begin(), clique.end());
    auto end_iter = std::unique(clique.begin(), clique.end());

    // Add clique weights to get upper bound
    NodeWeight upper_bound = 0;
    for (auto iter = clique.begin(); iter != end_iter; iter++) upper_bound += clique_weight[*iter];

    return upper_bound;
}

size_t branch_and_reduce_algorithm::run_ils(const MISConfig& config, graph_access& G, sized_vector<NodeID>& tmp_buffer,
                                            size_t max_swaps) {
    greedy_initial_is(G, tmp_buffer);
    ils local_search(config);
    local_search.perform_ils(G, max_swaps);

    size_t solution_weight = 0;

    forall_nodes (G, node) {
        if (G.getPartitionIndex(node) == 1) {
            solution_weight += G.getNodeWeight(node);
        }
    }
    endfor

    return solution_weight;
}

size_t branch_and_reduce_algorithm::run_ils_only(const MISConfig& config, graph_access& G, sized_vector<NodeID>& tmp_buffer,
                                            size_t max_swaps) {
    //greedy_initial_is(G, tmp_buffer);
    ils local_search(config);
    local_search.perform_ils(G, max_swaps);

    size_t solution_weight = 0;

    forall_nodes (G, node) {
        if (G.getPartitionIndex(node) == 1) {
            solution_weight += G.getNodeWeight(node);
        }
    }
    endfor

    return solution_weight;
}

void branch_and_reduce_algorithm::init_reduction_step() {
    if (!status.reductions[active_reduction_index]->has_run) {
        status.reductions[active_reduction_index]->marker.fill_current_ascending(status.n);
        status.reductions[active_reduction_index]->marker.clear_next();
        status.reductions[active_reduction_index]->has_run = true;
    } else {
        status.reductions[active_reduction_index]->marker.get_next();
    }
}

void branch_and_reduce_algorithm::add_next_level_node(NodeID node) {
    // mark node for next round of status.reductions
    for (auto& reduction : status.reductions) {
        if (reduction->has_run) {
            reduction->marker.add(node);
        }
    }
}

void branch_and_reduce_algorithm::add_next_level_nodes(const std::vector<NodeID>& nodes) {
    for (auto node : nodes) {
        add_next_level_node(node);
    }
}

void branch_and_reduce_algorithm::add_next_level_nodes(const sized_vector<NodeID>& nodes) {
    for (auto node : nodes) {
        add_next_level_node(node);
    }
}

void branch_and_reduce_algorithm::add_next_level_neighborhood(NodeID node) {
    // node has been excluded in mis -> neighboring vertices are interesting for next round of reduction
    for (auto neighbor : status.graph[node]) {
        add_next_level_node(neighbor);
    }
}

void branch_and_reduce_algorithm::add_next_level_neighborhood(const std::vector<NodeID>& nodes) {
    for (auto node : nodes) {
        add_next_level_neighborhood(node);
    }
}

void branch_and_reduce_algorithm::initial_reduce() {
    std::swap(global_reduction_map, local_reduction_map);
    status = std::move(global_status);
    reduce_graph_internal();
    // status.modified_queue.push_back(INITIAL_REDUCTION_TOKEN);

    global_status = std::move(status);
    std::swap(global_reduction_map, local_reduction_map);
}

void branch_and_reduce_algorithm::reduce_graph() {
    initial_reduce();
    status = std::move(global_status);
}

void branch_and_reduce_algorithm::reduce_graph_internal() {
    bool progress;

    do {
        // std::cout << "\ncurrent weight: " << status.is_weight << "  weight offset: " << status.reduction_offset
        // << " remaining nodes: " << status.remaining_nodes << std::endl;
        progress = false;

        for (auto& reduction : status.reductions) {
            active_reduction_index = local_reduction_map[reduction->get_reduction_type()];

            init_reduction_step();
            progress = reduction->reduce(this);

#ifndef NDEBUG
            if (status.is_node_lower_status_available) {
                for (NodeID node = 0; node < status.graph.size(); ++node) {
                    if (status.node_status[node] == IS_status::not_set) {
                        if (status.node_lower_status[node] == IS_status::excluded) {
                            bool found_sol_neighbor = false;
                            for (auto target : status.graph[node]) {
                                if (status.node_lower_status[target] == IS_status::included) {
                                    found_sol_neighbor = true;
                                    break;
                                }
                            }
                            if (!found_sol_neighbor) {
                                std::cout << reduction->get_reduction_type() << std::endl;
                                throw std::invalid_argument(std::string("not maximal"));
                            }
                        } else {
                            for (auto target : status.graph[node]) {
                                if (status.node_lower_status[target] == IS_status::included) {
                                    std::cout << reduction->get_reduction_type() << std::endl;
                                    throw std::invalid_argument(std::string("not independent"));
                                }
                            }
                        }
                    }
                }
            }
#endif

            if (progress) break;

            active_reduction_index++;
        }
    } while (progress);

    status.modified_queue.push_back(BRANCHING_TOKEN);

    // std::cout << "\ncurrent weight: " << status.is_weight << "  weight offset: " << status.reduction_offset << "
    // remaining nodes: " << status.remaining_nodes << std::endl;
}

bool branch_and_reduce_algorithm::branch_reduce_recursive() {
    //std::cout << "branch-recursive" << std::endl;
    build_graph_access(recursive_graph, recursive_mapping);
    size_t comp_count = strongly_connected_components().strong_components(recursive_graph, recursive_comp_map);

    if (comp_count == 1) return false;

    graph_extractor extractor;
    const auto time_limit = config.time_limit;

    ASSERT_TRUE(is_token(status.modified_queue.back()));
    status.modified_queue.pop_back();
    if(status.is_node_lower_status_available) {
        status.modified_lower_queue.pop_back();
    }

    for (size_t node = 0; node < status.remaining_nodes; node++) {
        recursive_graph.setPartitionIndex(node, recursive_comp_map[node] + 2);
    }

    for (size_t i = 0; i < comp_count; i++) {
        if (t.elapsed() > time_limit) {
            timeout = true;
            break;
        }

        recursive_local_mapping.clear();
        graph_access G;
        extractor.extract_block(recursive_graph, G, i + 2, recursive_local_mapping);

        if (status.is_node_lower_status_available) {
            std::vector<IS_status> node_init_sol(G.number_of_nodes(), IS_status::excluded);
            NodeWeight init_is_weight = 0;
            for (NodeID node = 0; node < G.number_of_nodes(); ++node) {
                // is node included in lower status
                if (status.node_lower_status[recursive_mapping[recursive_local_mapping[node]]] == IS_status::included) {
                    node_init_sol[node] = IS_status::included;
                    init_is_weight += G.getNodeWeight(node);
                }
            }

            // TODO wrapper
            config.time_limit = time_limit - t.elapsed();

            cout_handler::disable_cout();
            branch_and_reduce_algorithm br_alg(G, node_init_sol, init_is_weight, config, true);
            timeout = !br_alg.run_branch_reduce();
            cout_handler::enable_cout();

            if (timeout) break;

            br_alg.apply_branch_reduce_solution(G);
        } else {
            // TODO wrapper
            config.time_limit = time_limit - t.elapsed();

            cout_handler::disable_cout();
            branch_and_reduce_algorithm br_alg(G, config, true);
            timeout = !br_alg.run_branch_reduce();
            cout_handler::enable_cout();

            if (timeout) break;

            br_alg.apply_branch_reduce_solution(G);
        }

        forall_nodes (G, node) {
            recursive_graph.setPartitionIndex(recursive_local_mapping[node], G.getPartitionIndex(node));
        }
        endfor
    }

    config.time_limit = time_limit;

    if (timeout) {
        return false;
    }

    forall_nodes (recursive_graph, node) {
        if (recursive_graph.getPartitionIndex(node) == 1) set(recursive_mapping[node], IS_status::included);
    }
    endfor

    return true;
}

void branch_and_reduce_algorithm::branch_reduce_single_component() {
    best_weight = 0;
    len_non_impr_seq = 0;

    if (status.n == 0) {
        return;
    } else if (status.n == 1) {
        set(0, IS_status::included);

        std::cout << (get_current_is_weight() + status.is_weight + status.reduction_offset) << " [" << t.elapsed()
                  << "]" << std::endl;
        return;
    }

    sized_vector<NodeID> node_order(status.n);

    for (size_t node = 0; node < status.n; node++) {
        if (status.node_status[node] == IS_status::not_set) {
            node_order.push_back(node);
        }
    }

    std::sort(node_order.begin(), node_order.end(), [&](const NodeID lhs, const NodeID rhs) {
        return deg(lhs) > deg(rhs) || (deg(lhs) == deg(rhs) && status.weights[lhs] > status.weights[rhs]);
    });

    if (status.n > ILS_SIZE_LIMIT)
        compute_ils_pruning_bound();

    if (status.is_node_lower_status_available) {
// sanity check
// check whether lower solution is maximal wis
#ifndef NDEBUG
        std::cout << "debug" << std::endl;
        for (NodeID node = 0; node < local_graph->number_of_nodes(); ++node) {
            if (status.node_lower_status[node] == IS_status::excluded) {
                bool found_sol_neighbor = false;
                forall_out_edges ((*local_graph), e, node) {
                    auto target = local_graph->getEdgeTarget(e);
                    if (status.node_lower_status[target] == IS_status::included) {
                        found_sol_neighbor = true;
                        break;
                    }
                }
                endfor
                if (!found_sol_neighbor) {
                    throw std::invalid_argument(std::string("not maximal"));
                }
            } else {
                forall_out_edges ((*local_graph), e, node) {
                    auto target = local_graph->getEdgeTarget(e);
                    if (status.node_lower_status[target] == IS_status::included) {
                        throw std::invalid_argument(std::string("not independent"));
                    }
                }
                endfor
            }
        }
#endif

        if (status.is_lower_weight > best_weight) {
            std::cout << "init solution better: " << status.is_lower_weight - best_weight << std::endl;
            best_weight = status.is_lower_weight;
            is_ils_best_solution = false;
            is_init_best_solution = true;

            for (NodeID node = 0; node < local_graph->number_of_nodes(); ++node) {
                if (status.node_lower_status[node] != static_cast<bool>(local_graph->getPartitionIndex(node))) {
                    local_graph->setPartitionIndex(node, status.node_lower_status[node]);
                }
            }

        } else {
            std::cout << "ils solution better " << best_weight - status.is_lower_weight << std::endl;
            // do not use initial solution any longer
            status.is_node_lower_status_available = false;
        }
    }/*else if (status.n > ILS_SIZE_LIMIT) {
        compute_ils_pruning_bound();
    }*/

    /*if(is_init_best_solution) {
        cout_handler::disable_cout();

        auto config_cpy = config;
        config_cpy.time_limit = config_cpy.time_limit * status.n / total_ils_node_count / 100;

        NodeWeight old_weight = best_weight;
        best_weight = run_ils_only(config_cpy, *local_graph, buffers[0], 1000);

        cout_handler::enable_cout();
        std::cout << (get_current_is_weight() + best_weight) << " [" << t.elapsed() << "]" << std::endl;
        std::cout << "improved by "  << best_weight - old_weight << std::endl;
    }*/

    recursive_mapping.resize(status.n, 0);
    recursive_comp_map.resize(status.n, 0);

    size_t i = 0;
    while (i < status.n) {
        if (t.elapsed() > config.time_limit && best_weight != 0) {
            timeout = true;
            break;
        }

        /*if(len_non_impr_seq >= MAX_LEN_NON_IMPR_SEQ && best_weight != 0) {
            // timeout = true;
            break;
        }*/

        NodeID branch_node = node_order[i];

        if (i == status.n - 1) {
            if (status.node_status[branch_node] == IS_status::not_set) {
                set(branch_node, IS_status::included);

                if (status.is_node_lower_status_available) {
                    // zero commit, in order to be synchronous with modified_queue
                    status.modified_lower_queue.push_back(0);
                }
            }

            update_best_solution();
            reverse_branching();
            i = status.branching_queue.back().pos;
            continue;
        }

        bool improvement_possible = false;

        // upper bound can be more tight
        /*if(!status.branching_queue.empty() &&
            status.branching_queue.back().node == branch_node &&
            status.node_status[branch_node] == IS_status::included) {
            improvement_possible = status.is_weight + status.reduction_offset + compute_cover_pruning_bound() - status.weights[branch_node] > best_weight;
        }else {
            improvement_possible = status.is_weight + status.reduction_offset + compute_cover_pruning_bound() > best_weight;
        }*/
        improvement_possible = status.is_weight + status.reduction_offset + compute_cover_pruning_bound() > best_weight;

        if (improvement_possible && status.node_status[branch_node] == IS_status::not_set) {
            // first time reaching this node in this branch
            set(branch_node, IS_status::included, false);

            // update lower solution
            if (status.is_node_lower_status_available) {
                if (status.node_lower_status[branch_node] == IS_status::excluded) {
                    flip_include_exclude_lower(branch_node);
                } else {
                    status.modified_lower_queue.push_back(0);
                }
            }

            status.branching_queue.emplace_back(branch_node, i);
        } else if (improvement_possible && !status.branching_queue.empty() &&
                   status.branching_queue.back().node == branch_node) {
            if (status.node_status[branch_node] == IS_status::included) {
                // second time reaching this node in this branch
                flip_include_exclude(branch_node);

                if (status.is_node_lower_status_available) {
                    if (status.node_lower_status[branch_node] == IS_status::included) {
                        flip_include_exclude_lower(branch_node);
                    } else {
                        status.modified_lower_queue.push_back(0);
                    }
                }

            } else {
                // third time reaching this node in this branch
                status.branching_queue.pop_back();
                unset(branch_node);

                if (i == 0) break;

                reverse_branching();

                i = status.branching_queue.back().pos;
                continue;
            }
        } else if (!improvement_possible) {
            ++len_non_impr_seq;
            if (!status.branching_queue.empty() && status.branching_queue.back().node == branch_node) {
                status.branching_queue.pop_back();
                unset(branch_node);
                // if (i == 0) break;
            }
            // bug-fix: added case: if improvement not possible in the beginning, do not perform any branching at all
            // still covering case: first branch is not improving (line 698)
            if (i == 0) {
                ASSERT_TRUE(status.branching_queue.empty());
                break;
            }
            ASSERT_TRUE(!status.branching_queue.empty());

            reverse_branching();

            i = status.branching_queue.back().pos;
            continue;
        } else {
            i++;
            continue;
        }

        reduce_graph_internal();
        if (status.is_node_lower_status_available) {
            status.modified_lower_queue.push_back(BRANCHING_TOKEN);
        }

        if (status.remaining_nodes > SPLIT_CC_LIMIT && branch_reduce_recursive()) {
            status.modified_queue.push_back(BRANCHING_TOKEN);
            if (status.is_node_lower_status_available) {
                status.modified_lower_queue.push_back(BRANCHING_TOKEN);
            }
            update_best_solution();
            reverse_branching();
            i = status.branching_queue.back().pos;
        } else {
            i++;
        }
    }

    restore_best_local_solution();
    std::cout << "len_non_impr_seq: " << len_non_impr_seq << ", n: " << status.n << ", kor: " << (static_cast<double>(len_non_impr_seq) / status.n) << std::endl;
}

bool branch_and_reduce_algorithm::run_branch_reduce() {
    t.restart();
    initial_reduce();

    // std::cout << "%reduction_nodes " << global_status.remaining_nodes << "\n";
    // std::cout << "%reduction_offset " << global_status.is_weight + global_status.reduction_offset << "\n";
    std::cout << "reduction_time " << t.elapsed() << "\n";

    if (global_status.remaining_nodes == 0) {
        restore_best_global_solution();
        return true;
    }

    build_global_graph_access();

    std::vector<int> comp_map(global_status.remaining_nodes, 0);
    size_t comp_count = strongly_connected_components().strong_components(global_graph, comp_map);

    // std::cout << "%components " << comp_count << "\n";

    for (size_t node = 0; node < global_status.remaining_nodes; node++) {
        global_graph.setPartitionIndex(node, comp_map[node]);
    }

    std::vector<size_t> comp_size(comp_count, 0);
    for (auto comp_id : comp_map) {
        comp_size[comp_id]++;
    }

    total_ils_node_count = 0;
    std::vector<size_t> comp_idx(comp_count, 0);
    for (size_t i = 0; i < comp_count; i++) {
        comp_idx[i] = i;
        if (comp_size[i] > ILS_SIZE_LIMIT) {
            total_ils_node_count += comp_size[i];
        }
    }

    std::sort(comp_idx.begin(), comp_idx.end(),
              [&comp_size](const size_t lhs, const size_t rhs) { return comp_size[lhs] < comp_size[rhs]; });

    // std::cout << "%max_component " << comp_size[comp_idx.back()] << "\n";

    graph_extractor extractor;

    buffers.resize(7, sized_vector<NodeID>(global_status.n));

    for (size_t i : comp_idx) {
        if (t.elapsed() > config.time_limit) {
            timeout = true;
            break;
        }

        // std::cout << "%connected component " << i << ":  " << comp_size[i] << std::endl;

        local_mapping.clear();
        graph_access G;
        extractor.extract_block(global_graph, G, i, local_mapping);
        local_graph = &G;

        if (global_status.is_node_lower_status_available) {
            // extract lower solution for local_graph
            NodeWeight local_wis_weight = 0;
            for (NodeID node = 0; node < local_graph->number_of_nodes(); ++node) {
                local_lower_sol[node] = global_status.node_lower_status[global_mapping[local_mapping[node]]];
                if (local_lower_sol[node] == IS_status::included) {
                    local_wis_weight += local_graph->getNodeWeight(node);
                }
            }
            status = graph_status(*local_graph, local_lower_sol, local_wis_weight);
        } else {
            status = graph_status(*local_graph);
        }

        set_local_reductions();

        branch_reduce_single_component();

        for (size_t node = 0; node < status.n; node++) {
            // if (status.node_status[node] == IS_status::not_set || status.node_status[node] == IS_status::folded)
            // { 	std::cerr << "error: node is not_set / folded after restore" << std::endl; 	exit(1);
            // }

            global_status.node_status[global_mapping[local_mapping[node]]] = status.node_status[node];
        }

        global_status.is_weight += best_weight;
        global_status.remaining_nodes -= status.n;
        local_graph = nullptr;
    }

    if (timeout) {
        std::cout << "%timeout" << std::endl;
        fill_global_greedy();
    }

    restore_best_global_solution();
    return !timeout;
}

void branch_and_reduce_algorithm::update_best_solution() {
    NodeWeight current_weight = status.is_weight + status.reduction_offset;
    if (current_weight > best_weight) {
        best_solution_status = status;
        best_weight = current_weight;
        is_ils_best_solution = false;
        is_init_best_solution = false;
        std::cout << "impr len_non_impr_seq: " << len_non_impr_seq << ", n: " << status.n << ", kor: " << (static_cast<double>(len_non_impr_seq) / status.n) << std::endl;
        len_non_impr_seq = 0;

        std::cout << (get_current_is_weight() + current_weight) << " [" << t.elapsed() << "]" << std::endl;
    }else{
        ++len_non_impr_seq;
    }
}

void branch_and_reduce_algorithm::reverse_branching() {
    // discard topmost branching token
    if (!status.modified_queue.empty()) {
        ASSERT_TRUE(is_token(status.modified_queue.back()));
        status.modified_queue.pop_back();

        if (status.is_node_lower_status_available) {
            ASSERT_TRUE(is_token(status.modified_lower_queue.back()));
            status.modified_lower_queue.pop_back();
        }
    } else {
        return;
    }

    while (!status.modified_queue.empty() && !is_token(status.modified_queue.back())) {
        NodeID node = status.modified_queue.back();
        status.modified_queue.pop_back();

        if (status.node_status[node] == IS_status::folded) {
            // std::cout << "reversed fold" << std::endl;
            auto type = status.folded_queue.back();
            status.folded_queue.pop_back();
            status.reductions[local_reduction_map[type]]->restore(this);
            continue;
        }

        unset(node);
    }

    if (status.is_node_lower_status_available) {
        while (!status.modified_lower_queue.empty() && !is_token(status.modified_lower_queue.back())) {
            reverse_lower_modifications();
        }
    }
}

void branch_and_reduce_algorithm::restore_best_local_solution() {
    if (is_ils_best_solution || is_init_best_solution) {
        for (size_t node = 0; node < status.n; node++) {
            if (local_graph->getPartitionIndex(node) == 1) {
                status.node_status[node] = IS_status::included;
            } else {
                status.node_status[node] = IS_status::excluded;
            }
        }
        return;
    }

    status = best_solution_status;
    status.modified_queue.pop_back();

    while (!status.modified_queue.empty()) {
        NodeID node = status.modified_queue.back();
        status.modified_queue.pop_back();

        if (node == BRANCHING_TOKEN) {
            status.graph.restore_node(status.branching_queue.back().node);
            status.branching_queue.pop_back();
            continue;
        }

        if (status.node_status[node] == IS_status::folded) {
            auto type = status.folded_queue.back();
            status.folded_queue.pop_back();
            status.reductions[local_reduction_map[type]]->apply(this);
        } else {
            status.graph.restore_node(node);
        }
    }
}

void branch_and_reduce_algorithm::restore_best_global_solution() {
    status = std::move(global_status);
    status.modified_queue.pop_back();

    while (!status.modified_queue.empty()) {
        NodeID node = status.modified_queue.back();
        status.modified_queue.pop_back();

        if (status.node_status[node] == IS_status::folded) {
            auto type = status.folded_queue.back();
            status.folded_queue.pop_back();
            status.reductions[global_reduction_map[type]]->apply(this);
        } else {
            status.graph.restore_node(node);
        }
    }
}

NodeWeight branch_and_reduce_algorithm::get_current_is_weight() const {
    return global_status.is_weight + global_status.reduction_offset;
}

void branch_and_reduce_algorithm::build_global_graph_access() {
    global_mapping.resize(global_status.remaining_nodes, 0);
    std::swap(status, global_status);
    build_graph_access(global_graph, global_mapping);
    std::swap(status, global_status);
}

void branch_and_reduce_algorithm::build_graph_access(graph_access& G, std::vector<NodeID>& reverse_mapping) const {
    std::vector<NodeID> mapping(status.graph.size(), UINT_MAX);
    size_t edge_count = 0;

    // Get number of edges and reorder nodes
    size_t node_counter = 0;
    for (NodeID node = 0; node < status.graph.size(); ++node) {
        if (status.node_status[node] == IS_status::not_set) {
            for (auto neighbor : status.graph[node]) {
                edge_count++;
            }

            mapping[node] = node_counter;
            reverse_mapping[node_counter] = node;
            node_counter++;
        }
    }

    // Create the adjacency array
    std::vector<int> xadj(status.remaining_nodes + 1);
    std::vector<int> adjncy(edge_count + 1);
    size_t adjncy_counter = 0;

    for (size_t i = 0; i < status.remaining_nodes; ++i) {
        xadj[i] = adjncy_counter;

        for (auto neighbor : status.graph[reverse_mapping[i]]) {
            if (mapping[neighbor] == i) continue;
            if (mapping[neighbor] == UINT_MAX) continue;
            adjncy[adjncy_counter++] = mapping[neighbor];
        }

        std::sort(std::begin(adjncy) + xadj[i], std::begin(adjncy) + adjncy_counter);
    }
    xadj[status.remaining_nodes] = adjncy_counter;

    // Build the graph
    G.build_from_metis(status.remaining_nodes, &xadj[0], &adjncy[0]);

    forall_nodes (G, node) {
        G.setNodeWeight(node, status.weights[reverse_mapping[node]]);
    }
    endfor
}

void branch_and_reduce_algorithm::build_induced_neighborhood_subgraph(graph_access& G, NodeID source_node) {
    buffers[0].clear();
    set_1.clear();

    for (NodeID neighbor : status.graph[source_node]) {
        buffers[0].push_back(neighbor);
        set_1.add(neighbor);
    }

    build_induced_subgraph(G, buffers[0], set_1, buffers[1]);
}

void branch_and_reduce_algorithm::build_induced_subgraph(graph_access& G, const sized_vector<NodeID>& nodes,
                                                         const fast_set& nodes_set,
                                                         sized_vector<NodeID>& reverse_mapping) {
    size_t edge_count = 0;

    for (size_t i = 0; i < nodes.size(); i++) {
        NodeID node = nodes[i];
        for (auto neighbor : status.graph[node]) {
            if (nodes_set.get(neighbor)) edge_count++;
        }

        reverse_mapping[node] = i;
    }

    G.start_construction(nodes.size(), edge_count);

    for (NodeID node : nodes) {
        NodeID new_node = G.new_node();
        G.setNodeWeight(new_node, status.weights[node]);

        for (auto neighbor : status.graph[node]) {
            if (nodes_set.get(neighbor)) {
                G.new_edge(new_node, reverse_mapping[neighbor]);
            }
        }
    }

    G.finish_construction();
}

void branch_and_reduce_algorithm::reverse_reduction(graph_access& G, graph_access& reduced_G,
                                                    std::vector<NodeID>& reverse_mapping) {
    // build_global_graph_access();

    forall_nodes (reduced_G, node) {
        if (reduced_G.getPartitionIndex(node) == 1) {
            status.node_status[reverse_mapping[node]] = IS_status::included;
        } else {
            status.node_status[reverse_mapping[node]] = IS_status::excluded;
        }
    }
    endfor

    global_status = std::move(status);
    restore_best_global_solution();
    apply_branch_reduce_solution(G);
}

void branch_and_reduce_algorithm::apply_branch_reduce_solution(graph_access& G) {
    forall_nodes (G, node) {
        if (status.node_status[node] == IS_status::included) {
            G.setPartitionIndex(node, 1);
        } else {
            G.setPartitionIndex(node, 0);
        }
    }
    endfor
}
void branch_and_reduce_algorithm::set_lower(NodeID node, branch_and_reduce_algorithm::IS_status mis_status,
                                            bool push_modified) {
    if (mis_status == IS_status::included) {
        status.node_lower_status[node] = IS_status::included;
        if (push_modified) status.modified_lower_queue.push_back(node);
    } else if (mis_status == IS_status::excluded) {
        status.node_lower_status[node] = IS_status::excluded;
        if (push_modified) status.modified_lower_queue.push_back(node);
    }
}
void branch_and_reduce_algorithm::reverse_lower_modifications() {
    ASSERT_TRUE(!status.modified_lower_queue.empty());
    ASSERT_TRUE(status.modified_lower_queue.size() >= status.modified_lower_queue.back() + 1);

    auto modifications = status.modified_lower_queue.back();
    status.modified_lower_queue.pop_back();

    for (size_t i = 0; i < modifications; ++i) {
        auto node = status.modified_lower_queue.back();
        status.modified_lower_queue.pop_back();

        if (status.node_lower_status[node] == IS_status::included) {
            set_lower(node, IS_status::excluded, false);
        } else {
            ASSERT_TRUE(status.node_lower_status[node] == IS_status::excluded);
            set_lower(node, IS_status::included, false);
        }
    }
}

NodeID branch_and_reduce_algorithm::maximize_lower(std::vector<NodeID>& nodes) {
    NodeID changes = 0;

    // node order
    // TODO maybe other heuristic
    std::sort(nodes.begin(), nodes.end(),
              [&w = status.weights](const NodeID first, const NodeID second) { return w[first] > w[second]; });

    // maximize
    for (auto v : nodes) {
        ASSERT_TRUE(status.node_lower_status[v] == IS_status::excluded);
        bool add_node = true;
        for (auto u : status.graph[v]) {
            if (status.node_lower_status[u] == IS_status::included) {
                add_node = false;
                break;
            }
        }
        if (add_node) {
            set_lower(v, IS_status::included, true);
            ++changes;
        }
    }
    return changes;
}

void branch_and_reduce_algorithm::flip_include_exclude_lower(NodeID node) {
    NodeID changes = 1;
    if (status.node_lower_status[node] == IS_status::excluded) {
        set_lower(node, IS_status::included, true);

        set_3.clear();
        // TODO would be nice to reserve space
        std::vector<NodeID> lower_solution_candidates;
        for(auto neighbor : status.graph[node]) {
            // block neighbors of v; v itself cannot be reached from a neighbor (v was hidden before neighbor)
            set_3.add(neighbor);
        }
        for (auto neighbor : status.graph[node]) {
            if (status.node_lower_status[neighbor] == IS_status::included) {
                set_lower(neighbor, IS_status::excluded, true);
                ++changes;

                for (auto v : status.graph[neighbor]) {
                    if (status.node_lower_status[v] == IS_status::excluded && !set_3.get(v)) {
                        set_3.add(v);
                        lower_solution_candidates.push_back(v);
                    }
                }
            }
        }

        changes += maximize_lower(lower_solution_candidates);
    } else {
        // node is included
        set_lower(node, IS_status::excluded, true);

        // maximize lower solution
        std::vector<NodeID> lower_solution_candidates;
        lower_solution_candidates.reserve(status.graph[node].size());
        for (auto v : status.graph[node]) {
            if (status.node_lower_status[v] == IS_status::excluded) {
                lower_solution_candidates.push_back(v);
            }
        }
        changes += maximize_lower(lower_solution_candidates);
    }
    status.modified_lower_queue.push_back(changes);
}

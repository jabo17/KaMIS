#/bin/bash
log=$1
awk '{print $0;} /reduction_time/{exit 0;}' $log |awk -F, '/redu-stat/{a[$2]+=$3; b[$2]+=$4} END{for(k in a){print k, a[k], b[k];}}'

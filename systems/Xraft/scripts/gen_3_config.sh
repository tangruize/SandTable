#!/bin/bash

COUNT=${1:-3}
SUBNET=${2}
GEN_FILE=${3}

source $(dirname "$(realpath "$0")")/../../../scripts/env.sh && export CUR_SCRIPT_DIR=$(eval $(get_dir_cmd)) && export_more

check_vars COUNT SUBNET GEN_FILE

eval $GENERATE_CONFIG_SH -P -s $SUBNET -t traces.txt controller n{$(seq -s, 1 $COUNT)} > "$GEN_FILE"

# xraft specific config
cat <<EOF >> "$GEN_FILE"
log stdout node_log
log stderr node_log
collector /usr/bin/python3 $state_collector_py
option state_no_fail_empty
EOF

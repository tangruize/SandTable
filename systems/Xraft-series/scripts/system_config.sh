#!/bin/bash

source $(dirname "$(realpath "$0")")/env.sh
source $SYSTEM_CONFIG_COMMON_SH "$@"

# xraft specific config
cat <<EOF >> "$GEN_FILE"
log stdout node_log
log stderr node_log
collector /usr/bin/python3 $state_collector_py
option state_no_fail_empty
EOF

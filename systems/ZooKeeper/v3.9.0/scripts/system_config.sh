#!/bin/bash

source $(dirname "$(realpath "$0")")/env.sh
source $SYSTEM_CONFIG_COMMON_SH "$@"

cat <<EOF >> "$GEN_FILE"
log stdout node_log
log stderr node_log
collector /usr/bin/python3 $state_collector_py
option detail
option tmpdir
option multi_ports
option block_connect_timeout 3
option deliver_first_msg_ports 3888
option merge_small_msg 4
option no_exec_ack
option add_ssh_timeout 10
option abort_failed_init
#option state_no_clear
#option state_no_fail_empty
EOF

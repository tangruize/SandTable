#!/bin/bash

source $(dirname "$(realpath "$0")")/env.sh
source $SYSTEM_CONFIG_COMMON_SH "$@"

cat <<EOF >> "$GEN_FILE"
option partition_keep_msgs
option allow_msg_unordered
EOF
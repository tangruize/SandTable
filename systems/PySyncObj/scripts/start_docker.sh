#!/bin/bash

source $(dirname "$(realpath "$0")")/env.sh
source $START_DOCKER_COMMON_SH "$@"

HOST_CMD="$CONTROLLER -detail -config $CONFIG_FILE -tmpdir $TMPDIR -deliver_first_msg; exit"

cat <<EOF | "$SPSSH_SH" -H -S -q -t -e -s -r "$HOST_CMD" -w "$TMPDIR" root@n{1,2,3}
cd $TESTCASE_DIR
export PROGRAM_PATH=python3
$INTERCEPTOR_SH -config $CONFIG_FILE python3 "n\${SSH_NO}.py"; exit
EOF

source $WAIT_TMUX_COMMON_SH

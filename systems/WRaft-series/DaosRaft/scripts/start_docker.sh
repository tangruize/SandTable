#!/bin/bash

source $(dirname "$(realpath "$0")")/env.sh
source $START_DOCKER_COMMON_SH "$@"

CLIENT=$SANDTABLE_BUILD_DIR/drivers/DaosRaftDriver

HOST_CMD="$CONTROLLER -detail -config $CONFIG_FILE -tmpdir $TMPDIR; exit"

cat <<EOF | "$SPSSH_SH" -H -S -q -t -e -s -r "$HOST_CMD" -w "$TMPDIR" root@n{1,2}
cd $TESTCASE_DIR
export PROGRAM_PATH=$CLIENT
$INTERCEPTOR_SH -config $CONFIG_FILE $CLIENT -config $CONFIG_FILE -detail -name "n\${SSH_NO}"; exit
EOF

source $WAIT_TMUX_COMMON_SH

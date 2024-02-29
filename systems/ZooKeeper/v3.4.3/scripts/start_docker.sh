#!/bin/bash

source $(dirname "$(realpath "$0")")/env.sh
source $START_DOCKER_COMMON_SH "$@"

CLIENT=$CUR_SCRIPT_DIR/../zookeeper-3.4.3/start.sh

HOST_CMD="-r 'sudo timeout --foreground $TIMEOUT $CONTROLLER -detail -config $CONFIG_FILE -tmpdir $TMPDIR; exit'"

cat <<EOF | eval "$SPSSH_SH" -H -S -b -q -t -e -s $HOST_CMD -w "$TMPDIR" $TIMEOUT_ARG root@n{1,2,3}
cd $TESTCASE_DIR
export PROGRAM_PATH=java
$INTERCEPTOR_SH -config $CONFIG_FILE $CLIENT $CONFIG_FILE && exit
EOF

source $WAIT_TMUX_COMMON_SH
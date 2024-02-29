#!/bin/bash

TRACE=$1
SERVERS=${2:-3}
if [ -n "$2" ]; then
    shift 2
else
    shift 1
fi

check_vars "TRACE" "SERVERS"

TRACE_DIR=$(realpath $(dirname $TRACE))
TEST_DIR=$TRACE_DIR/test
TEST_TRACE=$TEST_DIR/trace
CONFIG_FILE=$TEST_DIR/config/config.txt
BACKEND=${BACKEND:-docker}
if [ "$BACKEND" = "lxc" ]; then
    SUBNET=10.2.0.0/24
    export CONTROLLER_NODE=${CONTROLLER_NODE:-sandtable-lxc}
    export NAMESERVER=${NAMESERVER:-@$(ip route show 0.0.0.0/0 dev eth0 | cut -d' '  -f3)}
    export MASQUERADE=${MASQUERADE:-$(ip route show 0.0.0.0/0 dev eth0 | sed -En -e 's/.*via ([0-9.]+) .*/\1/' -e 's,\.1$,.0/24,p')}
else
    SUBNET=10.1.0.0/24
    export CONTROLLER_NODE=${CONTROLLER_NODE:-controller}
fi

set -e
mkdir -p $TEST_DIR/config
cp $TRACE $TEST_TRACE
bash $system_config_sh ${SERVERS} ${SUBNET} $CONFIG_FILE
cd $TEST_DIR
python3 $testcase_generator_py -i -c $CONFIG_FILE $TEST_TRACE "$@"

env -u TMUX bash $start_docker_sh $TEST_DIR

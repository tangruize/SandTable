#!/bin/bash

TRACE=$1
check_vars "TRACE"

TRACE_DIR=$(realpath $(dirname $TRACE))
TEST_DIR=$TRACE_DIR/test
TEST_TRACE=$TEST_DIR/trace
CONFIG_FILE=$TEST_DIR/config/config.txt

set -e
mkdir -p $TEST_DIR/config
cp $TRACE $TEST_TRACE
bash $system_config_sh 3 10.1.0.0/24 $CONFIG_FILE
cd $TEST_DIR
python3 $testcase_generator_py -i -c $CONFIG_FILE $TEST_TRACE

env -u TMUX bash $start_docker_sh $TEST_DIR

#!/bin/bash

# This script exports some script locations and provides some common functions
# Usage: source $(dirname "$(realpath "$0")")/../../../scripts/env.sh && export CUR_SCRIPT_DIR=$(eval $(get_dir_cmd)) && export_more

get_dir_cmd() {
    echo 'cd -- "$( dirname -- "${BASH_SOURCE[0]}" )" &> /dev/null && pwd'
}

check_vars() {
    while [ "$#" -ge 1 ]; do
        if [ -z "$(eval echo \$"$1")" ]; then
            echo "Empty variable: $1"
            exit 1
        fi
        shift
    done
}

export_more() {
    check_vars "CUR_SCRIPT_DIR"
    export system_config_sh=$CUR_SCRIPT_DIR/system_config.sh
    export run_one_testcase_sh=$CUR_SCRIPT_DIR/run_one_testcase.sh
    export run_py=$CUR_SCRIPT_DIR/run.py
    export run_sh=$CUR_SCRIPT_DIR/run.sh
    export mc_ini=$CUR_SCRIPT_DIR/mc.ini
    export sim_ini=$CUR_SCRIPT_DIR/sim.ini
    export start_docker_sh=$CUR_SCRIPT_DIR/start_docker.sh
    export state_collector_py=$CUR_SCRIPT_DIR/state_collector.py
    export testcase_generator_py=$CUR_SCRIPT_DIR/testcase_generator.py
}

export SCRIPT_DIR=$(eval $(get_dir_cmd))
export PROJECT_DIR=$(dirname ${SCRIPT_DIR})

export BATCH_CONFIG_TPROXY_SH=${SCRIPT_DIR}/batch_config_tproxy.sh
export DOCKER_RSYNC_SH=${SCRIPT_DIR}/docker_rsync.sh
export ENV_SH=${SCRIPT_DIR}/env.sh
export GENERATE_CONFIG_SH=${SCRIPT_DIR}/generate_config.sh
export GETIP_SH=${SCRIPT_DIR}/getip.sh
export SPSSH_SH=${SCRIPT_DIR}/spssh.sh
export TLCWRAPPER_PY=${SCRIPT_DIR}/tlcwrapper.py
export TPROXY_SH=${SCRIPT_DIR}/tproxy.sh
export TRACE_READER_PY=${SCRIPT_DIR}/trace_reader.py

export SYSTEM_CONFIG_COMMON_SH=${SCRIPT_DIR}/common/system_config_common.sh
export RUN_ONE_TESTCASE_COMMON_SH=${SCRIPT_DIR}/common/run_one_testcase_common.sh
export START_DOCKER_COMMON_SH=${SCRIPT_DIR}/common/start_docker_common.sh
export WAIT_TMUX_COMMON_SH=${SCRIPT_DIR}/common/wait_tmux_common.sh

BUILD_DIR=.
if ! test -f /.dockerenv && ! test $BACKEND; then
    BUILD_DIR=build
fi
SANDTABLE_BUILD_DIR=$PROJECT_DIR/$BUILD_DIR/cmake-build-debug
export CONTROLLER=$SANDTABLE_BUILD_DIR/controller/controller
export INTERCEPTOR_SH=$SANDTABLE_BUILD_DIR/interceptor/run.sh

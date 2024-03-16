#!/bin/bash

source $(dirname "$(realpath "$0")")/../../../scripts/env.sh && export CUR_SCRIPT_DIR=$(eval $(get_dir_cmd)) && export_more

# set RUN_CMDS variable, which is an array of two cmds
function get_run_cmds() {
    python3 "$tlcwrapper_py" -d
    local run_cmds=$(python3 "$TLCWRAPPER_PY" -sg "$sim_ini")
    local ifsbak="$IFS"
    IFS=$'\n'
    RUN_CMDS=($run_cmds)
    IFS="$ifsbak"
}

function run() {
    # cd {{model dir}}
    eval ${RUN_CMDS[0]}
    if test -d "$PROJECT_DIR/venv"; then
        source "$PROJECT_DIR/venv/bin/activate"
    fi
    python3 $run_py . &
    PID_RUN_PY=$!
    bash -c "set -x; ${RUN_CMDS[1]} -tool" | tee MC.out
    trap "trap '' TERM INT" TERM INT
    trap "kill $PID_RUN_PY 2>/dev/null" EXIT
    local max_secs=60
    for ((i=0;i<$max_secs;i++)); do
        if kill -0 $PID_RUN_PY 2>/dev/null; then
            sleep 1
        else
            break
        fi
    done
    if test "$i" -eq $max_secs; then
#        kill $(ps -ef | grep model-simulation/run.py | grep -v grep | awk '{print $2}') 2>/dev/null
        kill $PID_RUN_PY  2>/dev/null
    fi
}

# See https://stackoverflow.com/questions/2683279/how-to-detect-if-a-script-is-being-sourced
function is_sourced() {
   if [ -n "$ZSH_VERSION" ]; then
       case $ZSH_EVAL_CONTEXT in *:file:*) return 0;; esac
   else  # Add additional POSIX-compatible shell names here, if needed.
       case ${0##*/} in dash|-dash|bash|-bash|ksh|-ksh|sh|-sh) return 0;; esac
   fi
   return 1  # NOT sourced.
}

if ! is_sourced; then
    get_run_cmds
    run
fi

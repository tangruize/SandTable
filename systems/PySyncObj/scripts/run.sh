#!/bin/bash

RUN_SH_DIR=$(dirname "$(realpath "$0")")

# set RUN_CMDS variable, which is an array of two cmds
function get_run_cmds() {
    local tlc_cmd_dir=$RUN_SH_DIR/../../deps/tlc-cmd
    python3 "$tlc_cmd_dir/tlcwrapper.py" -d
    local run_cmds=$(python3 "$tlc_cmd_dir/tlcwrapper.py" -sg $RUN_SH_DIR/pysyncobj-sim.ini)
    local ifsbak="$IFS"
    IFS=$'\n'
    RUN_CMDS=($run_cmds)
    IFS="$ifsbak"
}

function run() {
    # cd {{model dir}}
    eval ${RUN_CMDS[0]}
    python3 $RUN_SH_DIR/run.py . &
    PID_RUN_PY=$!
    bash -c "set -x; ${RUN_CMDS[1]} -tool" | tee MC.out
    local max_secs=5
    for ((i=0;i<$max_secs;i++)); do
        if kill -0 $PID_RUN_PY 2>/dev/null; then
            sleep 1
        else
            break
        fi
    done
    if test "$i" -eq $max_secs; then
        kill $PID_RUN_PY 2>/dev/null
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

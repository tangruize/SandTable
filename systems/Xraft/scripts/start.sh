#!/bin/bash

source $(dirname "$(realpath "$0")")/../../../scripts/env.sh && export CUR_SCRIPT_DIR=$(eval $(get_dir_cmd)) && export_more

TIMEOUT=60
CLIENT=$CUR_SCRIPT_DIR/../kv-store/start.sh

function usage() {
    echo "Usage: start.sh trace_xxx.dir"
    exit 1
}

TESTCASE_DIR=$1
if ! test -d "$TESTCASE_DIR"; then
    usage
fi
TESTCASE_DIR=$(realpath $TESTCASE_DIR)

export TMPDIR=$(mktemp -u -d -p $TESTCASE_DIR)
mkdir -p $TMPDIR
TIMEOUT_ARG="-T $TIMEOUT"

cd $TESTCASE_DIR
CONFIG_FILE=$(realpath config/config.txt)

HOST_CMD="-r 'sudo timeout --foreground $TIMEOUT $CONTROLLER -detail -config $CONFIG_FILE -tmpdir $TMPDIR -half_duplex_connection; exit'"

cat <<EOF | eval "$SPSSH_SH" -H -S -b -q -t -e -s $HOST_CMD -w "$TMPDIR" $TIMEOUT_ARG root@n{1,2,3}
cd $TESTCASE_DIR
export PROGRAM_PATH=java
$INTERCEPTOR_SH -config $CONFIG_FILE $CLIENT $CONFIG_FILE; exit
EOF
# tmux wait-for "$TMPDIR"
tmux attach

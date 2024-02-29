#!/bin/bash

TIMEOUT=60

PROJECT_DIR=$(realpath $(dirname "$(realpath "$0")")/../..)
CONTROLLER=$PROJECT_DIR/cmake-build-debug/controller/controller
INTERCEPTRO_SH=$PROJECT_DIR/cmake-build-debug/interceptor/run.sh
SPSSH_SH=$PROJECT_DIR/deps/spssh/spssh.sh
CLIENT=$PROJECT_DIR/kv-store/start.sh

function usage() {
    echo "Usage: start-lxd.sh [-debug] [-attach] trace_xxx.dir"
    exit 1
}

# arg parse
while [ "${1:0:1}" = "-" ]; do
    case "$1" in
        -d | -debug | --debug-mode)
            DEBUG=true
            shift
            ;;
        -a | -attach | --attach-tmux)
            TMUX_ATTACH=true
            shift
            ;;
        -A | -attach-cmd | --print-attach-cmd)
            PRINT_ATTACH_CMD=true
            shift
            ;;
        *)
            usage
            ;;
    esac
done

TESTCASE_DIR=$1
if ! test -d "$TESTCASE_DIR"; then
    usage
fi
TESTCASE_DIR=$(realpath $TESTCASE_DIR)

if test "$DEBUG" = true; then
    export TMPDIR=/tmp/tmet/debug
else
    export TMPDIR=$(mktemp -u -d -p $TESTCASE_DIR)
    TIMEOUT_ARG="-T $TIMEOUT"
fi
mkdir -p $TMPDIR

cd $TESTCASE_DIR
CONFIG_FILE=$(realpath config/config.txt)

if test "$DEBUG" != true; then
    HOST_CMD="-r 'sudo timeout --foreground $TIMEOUT $CONTROLLER -detail -config $CONFIG_FILE -tmpdir $TMPDIR -half_duplex_connection; exit'"
fi

cat <<EOF | eval "$SPSSH_SH" -H -S -b -q -t -e -s $HOST_CMD -w "$TMPDIR" $TIMEOUT_ARG root@tangruize-node{1,2,3}.tang.lxd
cd $TESTCASE_DIR
export PROGRAM_PATH=java
$INTERCEPTRO_SH -config $CONFIG_FILE $CLIENT $CONFIG_FILE; exit
EOF
#if test "$TMUX_ATTACH" = true; then
#    test -t 0 && tmux attach -t SPSSH$(echo -n $TMPDIR | tail -c 2)>/dev/null
#elif test "$PRINT_ATTACH_CMD" = true; then
#    echo "To attach tmux: tmux attach -t SPSSH$(echo -n $TMPDIR | tail -c 2)"
#fi
tmux wait-for "$TMPDIR"

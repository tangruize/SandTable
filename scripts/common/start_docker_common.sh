#!/bin/bash

TIMEOUT=60

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

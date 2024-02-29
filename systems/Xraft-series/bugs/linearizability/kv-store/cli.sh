#!/bin/bash

# cli.sh n1 get
# cli.sh n2 put 2

set -e
SCRIPT_DIR=$(dirname "$(realpath "$0")")

node=${1/n/}
cmd=$2
cmd_value=$3
ip=$(dig +short n${node})
$SCRIPT_DIR/bin/xraft-kvstore-cli -${cmd} $cmd_value -gc ${1},${ip},3333 | grep -v DEBUG

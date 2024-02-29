#!/bin/bash

set -xe

CONFIG_FILE=${CONFIG_FILE:-$1}
test $SSH_NO
test $CONFIG_FILE

SCRIPT_DIR=$(dirname "$(realpath "$0")")

nodes=($(dig +short n{1,2,3} | sed "$(sed -En -e 's,.0/24,,g' -e 's/map-cidr (.*) (.*)/s,\2,\1,g/p' $CONFIG_FILE)"))

#export LD_DEBUG=all

java -cp "$SCRIPT_DIR/lib/*" -Dlog4j.configurationFile="$SCRIPT_DIR/conf/log4j2.xml" in.xnnyygn.xraft.kvstore.server.ServerLauncher \
    -gc n1,${nodes[0]},2333 n2,${nodes[1]},2333 n3,${nodes[2]},2333 -m group-member -i n$SSH_NO -p2 3333

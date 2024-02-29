#!/bin/bash

COUNT=${1:-3}
SUBNET=${2}
GEN_FILE=${3}
CONTROLLER_NODE=${CONTROLLER_NODE:-controller}

check_vars COUNT SUBNET GEN_FILE

eval $GENERATE_CONFIG_SH -P -b dig -s $SUBNET -t traces.txt ${CONTROLLER_NODE} n{$(seq -s, 1 $COUNT)} > "$GEN_FILE"

#!/bin/bash

COUNT=${1:-3}
SUBNET=${2}
GEN_FILE=${3}

check_vars COUNT SUBNET GEN_FILE

eval $GENERATE_CONFIG_SH -P -s $SUBNET -t traces.txt controller n{$(seq -s, 1 $COUNT)} > "$GEN_FILE"

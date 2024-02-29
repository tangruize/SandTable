#!/bin/bash

TPROXY_SCRIPT=$(dirname "$(realpath "$0")")/tproxy.sh

BACKEND=lxc
NUM=20

function usage() {
    echo "Usage: $0 [-n num] [-b backend] -c controller start/stop"
    exit 1
}

# arg parse
while [ "${1:0:1}" = "-" ]; do
    case "$1" in
        -n | -num | --num-of-subnets)
            NUM="$2"
            shift 2
            ;;
        -c | -controller | --controller-name)
            CONTROLLER="$2"
            shift 2
            ;;
        -b | -backend | --backend)
            BACKEND="$2"
            shift 2
            ;;
        -p | -prefix | --ip-prefix-num)
            PREFIX="$2"
            shift 2
            ;;
        *)
            usage
            ;;
    esac
done

if test -z "$PREFIX"; then
    if test "$BACKEND" = 'lxc'; then
        PREFIX=2
    else
        PREFIX=1
    fi
fi

if test $NUM -ge 100; then
    echo "NUM is too big: $NUM"
    exit
fi

CMD=$1

if test -z "$CONTROLLER" -o -z "$CMD"; then
    usage
fi

function get_subnet() {
    local n=$1
    echo -n 10.$PREFIX.$n.0/24
}

function get_port() {
    local n=$1
    echo 10$PREFIX$(printf '%02d' $n)
}

for ((i=0;i<$NUM;i++)); do
    sudo $TPROXY_SCRIPT -b $BACKEND -s $(get_subnet $i) -p $(get_port $i) -c $CONTROLLER $CMD
done
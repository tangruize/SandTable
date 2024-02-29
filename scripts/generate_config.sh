#!/bin/bash

function usage() {
    echo 'Usage: generate_config.sh -subnet SUBNET -trace TRACE_FILE [-backend docker/lxc/dig] [-masquerade SUBNET] CONTAINER_NAME ..'
    exit 1
}

function check_args() {
    while [ "$#" -ge 1 ]; do
        if [ -z "$1" ]; then
            usage
        fi
        shift
    done
}

GETIP_SH=$(dirname "$(realpath "$0")")/getip.sh

while [ "${1:0:1}" = "-" ]; do
    case "$1" in
        -s | -subnet | --virtual-subnet)
            SUBNET="$2"
            shift 2
            ;;
        -t | -trace | --trace-file)
            TRACE_FILE="$2"
            shift 2
            ;;
        -b | -backend | --backend)
            BACKEND="$2"
            shift 2
            ;;
        -m | -masquerade | --masquerade-subnet)
            MASQUERADE="$2"
            shift 2
            ;;
        -p | -port | --port)
            PORT="$2"
            shift 2
            ;;
        -P | -node-port | --node-port)
            NODE_PORT=true
            shift
            ;;
        *)
            usage
            ;;
    esac
done

function subnet_to_port() {
#    sed -E -e 's/\.//g' -e 's,(.*)/.*,\1,' <<<$SUBNET
    awk 'BEGIN { FS="[./]" } { printf "%d%d%02d",$1,$2,$3 }' <<<$SUBNET
}

if test -z "$PORT"; then
    PORT=$(subnet_to_port)
fi

if ! test "$1"; then
    usage
fi

check_args "$SUBNET" "$TRACE_FILE"

echo "map-cidr $SUBNET ${MASQUERADE:-10.255.255.0/24}"
echo "strategy file $TRACE_FILE"
#echo "strategy cmd"

if test -z "$BACKEND"; then
    if ! test -f "/.dockerenv"; then
        BACKEND=docker
    else
        BACKEND=dig
    fi
fi

if test "$NODE_PORT" = true; then
    $GETIP_SH -f -b "$BACKEND" -p "$PORT" $@ | sed -E '/^node/s/$/:'"$PORT"'/'
else
    $GETIP_SH -f -b "$BACKEND" -p "$PORT" $@
fi

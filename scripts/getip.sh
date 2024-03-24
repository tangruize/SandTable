#!/bin/bash

#set -x
function usage() {
    echo "Usage: getip.sh [-format] [-backend lxc/docker/dig] [-port router_port] [-nameserver @x]"
    echo "                [-family inet/inet6] [-interface eth0/enp5s0] [-scope global/local/link]"
    echo "                CONTAINER_NAME .."
    exit 1
}

function get_lxc_container_ip() {
    local container=$1
    local family=${2:-inet}
    local interface=\"${3:-'eth0", "enp5s0'}\"
    local scope=${4:-global}
    lxc list --format json |
        jq -re 'try .[] | select (.name == "'"$container"'") | .state.network | to_entries[]
            | select(.key == ('"$interface"')).value.addresses[]
            | select((.family == "'"$family"'") and (.scope == "'"$scope"'")) | .address'
}

function get_docker_container_ip() {
    local container=$1
    docker inspect "$container" | jq -re 'try .[].NetworkSettings.Networks | to_entries[].value.IPAddress'
}

function get_node_id() {
    local name=$1
    sed -En 's/.*(node|n)([0-9]+).*/n\2/p' <<< "$name"
}

BACKEND=${BACKEND:-lxc}
ROUTER_PORT='{{PORT}}'

# arg parse
while [ "${1:0:1}" = "-" ]; do
    case "$1" in
        -f | -format | --format-as-config)
            IS_FORMAT=true
            shift
            ;;
        -b | -backend | --backend)
            BACKEND="$2"
            shift 2
            ;;
        -p | -port | --router-port)
            ROUTER_PORT="$2"
            shift 2
            ;;
        -F | -family | --address-family)
            FAMILY="$2"
            shift 2
            ;;
        -I | -interface | --network-interface)
            INTERFACE="$2"
            shift 2
            ;;
        -S | -scope | --route-scope)
            SCOPE="$2"
            shift 2
            ;;
        -n | -nameserver | --nameserver)
            NAMESERVER="$2"
            shift 2
            ;;
        *)
            usage
            ;;
    esac
done

set -o pipefail
EXIT_STATUS=0

if ! test "$1"; then
    usage
fi

while test "$1"; do
    CONTAINER="$1"

    if test "$BACKEND" = docker; then
        IP=$(get_docker_container_ip "$CONTAINER" | head -1)
    elif test "$BACKEND" = lxc; then
        IP=$(get_lxc_container_ip "$CONTAINER" "$FAMILY" "$INTERFACE" "$SCOPE" | head -1)
    else
        IP=$(dig ${NAMESERVER} -4 +short "$CONTAINER" | head -1)
    fi
    _EXIT_STATUS=$?

    if test "$EXIT_STATUS" -eq 0; then
        EXIT_STATUS=$_EXIT_STATUS
    fi

    if test "$_EXIT_STATUS" -eq 0; then
        if test "$IS_FORMAT" = true; then
            NODE_ID=$(get_node_id "$CONTAINER")
            if test -z "$NODE_ID"; then
                echo "router $IP:$ROUTER_PORT"
            else
                echo "node $NODE_ID $IP"
            fi
        else
            echo "$IP"
        fi
    fi

    shift
done

exit $EXIT_STATUS

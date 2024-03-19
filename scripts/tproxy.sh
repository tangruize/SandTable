#!/bin/bash

#set -x
function usage() {
    echo "Usage: sudo $0 -backend [lxc/docker] -controller CONTAINER_NAME [-port TPROXY_PORT] [-subnet VIRTUAL_SUBNET] start/stop"
    exit 1
}

# check variables not null
function check_args() {
    while [ "$#" -ge 1 ]; do
        if [ -z "$1" ]; then
            usage
        fi
        shift
    done
}

function check_firewall_type() {
    backend=$1
    if test "$backend" = docker; then
        echo iptables
        return
    fi
    if command -v nft &> /dev/null && nft list table inet lxd &> /dev/null; then
        echo nft
    elif command -v iptables-legacy &> /dev/null && iptables-legacy -L -n | grep -q 'generated for LXD'; then
        echo iptables-legacy
    else
        echo 1>&2 Error: cannot detect LXD firewall type, make sure lxd is running, and nft/iptables-legacy are installed.
        exit 1
    fi
}

function check_cmd() {
    cmd=$1
    if ! command -v "$cmd" &> /dev/null; then
        echo 1>&2 Error: cannot find "$cmd"
        exit 1
    fi
}

function get_nft_handle() {
    local subnet=$1
    nft -a list chain inet lxd pstrt.lxdbr0 | sed -En '\,'"${subnet}"',s,.*# handle ([0-9]+),\1,p'
}

function delete_iptables_no_nat_rule() {
    local firewall_cmd=$1
    if test "$firewall_cmd" = nft; then
        get_nft_handle "$SUBNET" | xargs -trL 1 nft delete rule inet lxd pstrt.lxdbr0 handle
    else
        "${firewall_cmd}"-save -t nat | sed -En '\,'"${SUBNET//./\\.}"',s,^-A,-D,p' | xargs -trL 1 "${firewall_cmd}" -t nat
    fi
}

function add_iptables_no_nat_rule() {
    local firewall_cmd=$1
    if test "$firewall_cmd" = nft; then
        nft insert rule inet lxd pstrt.lxdbr0 ip daddr "$SUBNET" accept
    else
        "${firewall_cmd}" -t nat -I POSTROUTING -d "${SUBNET}" -j ACCEPT
    fi
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

function get_controller_ip() {
    local backend=$1
    local controller=$2
    if test "$backend" = docker; then
        docker inspect "$controller" | jq -re 'try .[].NetworkSettings.Networks | to_entries[].value.IPAddress' |  head -1
    else
        get_lxc_container_ip "$controller" | head -1
    fi
}

function get_ip_interface() {
    local controller_ip=$1
    ip route get "$controller_ip" | head -1 | cut -d' ' -f3
}

function check_root_permissoin() {
    if [ "$USER" != root ]; then
        echo "Error: Must run as root!"
        usage
        exit 1
    fi
}

check_root_permissoin

# for scripts to replace default value
CONTROLLER=${CONTROLLER}
PORT=${PORT}
SUBNET=${SUBNET}
BACKEND=${BACKEND}

# default value
CONTROLLER=${CONTROLLER:-controller}
SUBNET=${SUBNET:-10.1.1.0/24}
PORT=${PORT:-10110}
BACKEND=${BACKEND:-lxc}

# arg parse
while [ "${1:0:1}" = "-" ]; do
    case "$1" in
        -p | -port | --tproxy-port)
            PORT="$2"
            shift 2
            ;;
        -s | -subnet | --virtual-subnet)
            SUBNET="$2"
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
        *)
            usage
            ;;
    esac
done

check_args "$PORT" "$SUBNET" "$CONTROLLER"
check_cmd "$BACKEND"
PRIV_OR_SEP=$(test "$BACKEND" = docker && printf '%s' "--privileged" || printf '%s' "--")
FIREWALL_CMD=$(check_firewall_type "$BACKEND")
check_cmd "$FIREWALL_CMD"

# exit on failure
set -eo pipefail

CONTROLLER_IP=$(get_controller_ip "$BACKEND" "$CONTROLLER")
INTERFACE=$(get_ip_interface "$CONTROLLER_IP")

case "$1" in
    start)
        set -x
        # add route controller to local (not forward)
        "${BACKEND}" exec $PRIV_OR_SEP "$CONTROLLER" ip route add local "${SUBNET}" dev lo
        # tproxy iptables rule in controller node
        "${BACKEND}" exec $PRIV_OR_SEP "$CONTROLLER" iptables -t mangle -A PREROUTING -d "${SUBNET}" -p tcp -m tcp -j TPROXY --on-port "${PORT}" --on-ip 127.0.0.1
        "${BACKEND}" exec $PRIV_OR_SEP "$CONTROLLER" iptables -t mangle -A PREROUTING -d "${SUBNET}" -p udp -m udp -j TPROXY --on-port "${PORT}" --on-ip 127.0.0.1
        # add route host to controller
        ip route add "$SUBNET" via "$CONTROLLER_IP" dev "${INTERFACE}"
        # enable ip forwarding
        sysctl -w net.ipv4.ip_forward=1 > /dev/null
        # not to do network address translation (NAT) for this subnet
        delete_iptables_no_nat_rule "$FIREWALL_CMD"
        add_iptables_no_nat_rule "$FIREWALL_CMD"
        ;;
    stop)
        set +e
        set -x
        ip route del "${SUBNET}" dev "${INTERFACE}"
        delete_iptables_no_nat_rule "$FIREWALL_CMD"
        "${BACKEND}" exec $PRIV_OR_SEP "$CONTROLLER" ip route del local "${SUBNET}" dev lo
        "${BACKEND}" exec $PRIV_OR_SEP "$CONTROLLER" iptables -t mangle -D PREROUTING -d "${SUBNET}" -p tcp -m tcp -j TPROXY --on-port "${PORT}" --on-ip 127.0.0.1
        "${BACKEND}" exec $PRIV_OR_SEP "$CONTROLLER" iptables -t mangle -D PREROUTING -d "${SUBNET}" -p udp -m udp -j TPROXY --on-port "${PORT}" --on-ip 127.0.0.1
        ;;
    *)
        usage
        ;;
esac

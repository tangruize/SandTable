#!/bin/bash

RUN_SH_DIR=$(dirname "$(realpath "$0")")
CURRENT_DIR=$(realpath .)

dns_prefix=n
dns_suffix=

myid=$SSH_NO

if [ -z "$myid" ]; then
    echo SSH_NO is not set
    exit 1
fi

CONFIG_FILE=$1

if [ -z "$CONFIG_FILE" ]; then
    echo CONFIG_FILE is not set
    exit
fi

if [ "$2" = "real-addr" ]; then
    REAL_ADDR=1
fi

#lib_dir="$RUN_SH_DIR/lib"
libs="$RUN_SH_DIR/zookeeper-3.4.3.jar:$RUN_SH_DIR/lib/*:$RUN_SH_DIR/conf"
#conf_dir="$RUN_SH_DIR/myconf"
#config_file="$conf_dir/server$myid.cfg"
server_dir="$CURRENT_DIR/data/$myid"
log_file="log_dir/zookeeper.log"

#rm -rf "$server_dir"
mkdir -p "$server_dir"
echo $myid > "$server_dir/myid"

FLE_MIN_NOT=200
FLE_MAX_NOT=210

get_addr() {
    local id=$1
    if [ "$id" = "$myid" ]; then
        echo "0.0.0.0"
        return
    fi
    local addr="$dns_prefix$id$dns_suffix"
    local result=$(dig +short "$addr")
    if [ -z "$result" ]; then
        echo Cannot dig "$addr"
        exit 1
    fi
    if [ -n "$REAL_ADDR" ]; then
        echo "$result"
    else
        echo "$result" | sed "$(sed -En -e 's,.0/24,,g' -e 's/map-cidr (.*) (.*)/s,\2,\1,g/p' $CONFIG_FILE)"
    fi
}

config_file="$server_dir/config.cfg"

cat > "$config_file" <<EOF
tickTime=2000
initLimit=1
syncLimit=1
dataDir=$server_dir
clientPort=2180
server.1=$(get_addr 1):2888:3888
server.2=$(get_addr 2):2888:3888
server.3=$(get_addr 3):2888:3888
EOF

export PROGRAM_PATH=java

$PROGRAM_PATH \
    -Dzookeeper.log.dir="$server_dir" \
    -Dzookeeper.log.file="$log_file" \
    -Dzookeeper.root.logger="TRACE,CONSOLE" \
    -XX:+HeapDumpOnOutOfMemoryError \
    -XX:OnOutOfMemoryError='kill -9 %p' \
    -cp "$libs" \
    -Xmx1000m \
    -Dcom.sun.management.jmxremote \
    -Dcom.sun.management.jmxremote.local.only=false \
    -Dzookeeper.fastleader.minNotificationInterval="$FLE_MIN_NOT" \
    -Dzookeeper.fastleader.maxNotificationInterval="$FLE_MAX_NOT" \
    org.apache.zookeeper.server.quorum.QuorumPeerMain \
    "$config_file"

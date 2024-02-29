# SandTable

NOTICE: This repository is currently under construction and contains only Xraft and Xraft-KVStore. We will update other systems soon.

## Build

To avoid dependency issues, we recommend using an LXD container to run SandTable. Below is an example of creating an Ubuntu LXD container:

```sh
sudo snap install lxd
sudo lxd init --auto
lxc init ubuntu:22.04 ubuntu22
lxc config set ubuntu22 security.nesting=true
lxc start ubuntu22
lxc shell ubuntu22  # Enter ubuntu22 shell
```

Install dependencies (inside ubuntu22):

```sh
sudo apt-get update
sudo apt-get install -y docker.io docker-compose git iptables make jq
```

Build:

```sh
git clone https://github.com/tangruize/SandTable.git
cd SandTable
make start-docker
#make stop-docker  # To stop docker
```

## Replay Bugs

Check Xraft#1 (violates election safety):

```sh
make check_xraft_election_bug
```

Replay Xraft#1:

```sh
make replay_xraft_election_bug
```

Check and Replay Xraft-KV#1 (violates linearizability):

```sh
make check_xraft_kv_linearizability_bug
make replay_xraft_kv_linearizability_bug
```

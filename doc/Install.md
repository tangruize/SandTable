# Installation

Below are the directions to install and run SandTable.

We recommend running SandTable on a fresh Ubuntu environment (at least 20.04, preferably version 22.04 or later). Setting up an Ubuntu 22.04 container using LXD is simple. However, LXD is not always necessary if your system already runs Ubuntu 20.04 or a more recent version.

## Running SandTable inside an Ubuntu 22.04 LXD container

We recommend using an LXD container to run SandTable to avoid dependency issues. If you prefer not to install LXD, you can treat your Linux host as the container `sandtable-lxc`.

If you do not have a Linux environment to run LXD yet, please refer to [Install-Linux.md](./Install-Linux.md).

### Installing and configuring LXD container

To install and configure LXD, follow these steps:

```sh
sudo snap install lxd
## For storage drivers. It is OK to install one of them (e.g., ZFS is not supported on WSL2)
sudo apt-get install zfsutils-linux btrfs-progs
## Choose the default for most options. For storage, if Ubuntu host >= 23.10, choose ZFS; otherwise choose BTRFS
sudo lxd init
## Ensure the current user is added to the lxd group
sudo usermod -a -G lxd "$USER"  # log out and re-login
## Check if the storage is correctly configured
lxc storage list  # the DRIVER should be `zfs` or `btrfs`
## If the driver is `dir`, let's create a btrfs driver; otherwise, no need to create
lxc storage create btrfs btrfs size=40GiB
```

To initialize an Ubuntu 22.04 LXD container:

```sh
## We can change a fast mirror and use `mirror-ubuntu:22.04` instead of `ubuntu:22.04`. For example:
#lxc remote add mirror-ubuntu https://mirrors.nju.edu.cn/ubuntu-cloud-images/releases/ --protocol=simplestreams --public
## If we manually created a btrfs driver, add `-s btrfs` option after the `lxc init ..` command
## Note that the virtual machine image version in LXD has problems running SandTable, so do not add `--vm` option after `lxc init ..`
lxc init ubuntu:22.04 sandtable-lxc # -s btrfs
## Enable nesting to run Docker inside LXD containers
lxc config set sandtable-lxc security.nesting=true
lxc start sandtable-lxc
## Enter the sandtable-lxc shell (For root shell, run `lxc shell sandtable-lxc`)
lxc exec sandtable-lxc -- su -l ubuntu
```

### Configuring SandTable

In this section, we'll configure SandTable on Docker. For detailed configuration processes on other POSIX systems like OpenBSD, please refer to [Install-OpenBSD.md](./Install-OpenBSD.md).

To install dependencies (inside sandtable-lxc):

```sh
sudo apt-get update
sudo apt-get install -y docker.io docker-compose rsync git iptables make jq
```

To build Docker (inside sandtable-lxc):

```sh
## Ensure the current user is added to the docker group
sudo usermod -a -G docker "$USER"  # log out and re-login
git clone https://github.com/tangruize/SandTable.git
cd SandTable
make build-docker
```

To start Docker (inside sandtable-lxc):

```sh
## It will automatically compile SandTable and configure TPROXY
make start-docker
```

## Reproducing bugs

Here we provide some examples to reproduce bugs. For details, please refer to [Reproduce-Bugs.md](./Reproduce-Bugs.md)

The Makefile targets start with `check-` are designed for checking bugs at the specification level.
For example, to check the Xraft multiple valid Leader bug (inside sandtable-lxc):

```sh
make check_xraft_election_safety_bug
```

It will display the bug trace (which may differ from the following):

```json
["Init",3]
["ElectionTimeout","n1"]
["RecvRequestVote","voted","n3","n1"]
["ElectionTimeout","n1"]
["RecvRequestVoteResponse","become leader","n1","n3"]
["ElectionTimeout","n3"]
["RecvRequestVote","voted","n2","n3"]
["RecvRequestVoteResponse","become leader","n3","n2"]
```

The Makefile targets start with `replay-` is designed for replaying bugs at the implementation level.
For example, to replay the Xraft multiple valid Leader bug (inside sandtable-lxc):

```sh
make replay_xraft_election_safety_bug
```

It will provide information about the bug:

```txt
grep -r "become leader, term" build/mount/systems/Xraft-series/bugs/election_safety/test/log*
build/mount/systems/Xraft-series/bugs/election_safety/test/log.1:2022-06-04 05:36:58.200 [node] INFO  node.NodeImpl - become leader, term 2
build/mount/systems/Xraft-series/bugs/election_safety/test/log.3:2022-06-04 05:36:54.100 [node] INFO  node.NodeImpl - become leader, term 2
```

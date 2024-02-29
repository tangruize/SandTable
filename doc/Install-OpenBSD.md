# Setting Up OpenBSD Nodes

The interceptor of SandTable supports intercepting POSIX APIs. Below, we provide an example of running the interceptor on OpenBSD virtual machines.

The benefit of running the interceptor on OpenBSD: Some languages (like Golang) bypass system calls from libc for performance on Linux, rendering SandTable's interceptor unable to intercept programs written in such languages. On OpenBSD, bypassing system calls from libc is prohibited, thus ensuring SandTable's interceptor can always function effectively.

## Installing OpenBSD on LXD

We will reuse the `sandtable-lxc` container (please refer to [Install.md](./Install.md)) to run SandTable's engine (i.e., `src/controller`) and install OpenBSD on LXD to run SandTable's interceptor.

<details>
<summary>If your host cannot install dependencies in this tutorial, you can initialize LXD inside the sandtable-lxc container.</summary>

```bash
## (Execute on host)
## nesting for running nested containers
lxc config set sandtable-lxc security.nesting=true
## unconfined apparmor for LXD to start qemu with an extra boot device
lxc config set sandtable-lxc raw.lxc="lxc.apparmor.profile=unconfined"
## privileged for LXD to initialize the network if apparmor is unconfined, and for BTRFS to get full permissions
lxc config set sandtable-lxc security.privileged=true 
## pass devices related to LXD VM through sandtable-lxc
for device in kvm vsock vhost-net vhost-vsock; do lxc config device add sandtable-lxc $device unix-char path=/dev/$device mode=0666; done
```

```bash
## The ubuntu:22.04 image has preinstalled LXD
#sudo snap refresh lxd --channel=latest/stable
## Initialize LXD (inside sandtable-lxc)
### Choose BTRFS storage is available, otherwise choose DIR.
### Do not choose ZFS as nested LXD has issues in creating VMs in ZFS
sudo lxd init
## Create a nested sandtable-lxc container
lxc init ubuntu:22.04 sandtable-lxc
## Now treat the host/sandtable-lxc container as host and host/sandtable-lxc/sandtable-lxc as sandtable-lxc
```

</details>

Below are instructions to create an OpenBSD virtual machine on LXD (Execute on host, thanks to the excellent [tutorial](https://tobhe.de/stuff/lxd-openbsd.html)):

```bash
## Init an empty virtual machine
lxc init n1 --empty --vm -c limits.cpu=4 -c limits.memory=4GiB -c security.secureboot=false
## Configure the disk size (optional)
lxc config device override n1 root size=20GiB
## Fetch OpenBSD installer
wget https://ftp.openbsd.org/pub/OpenBSD/7.4/amd64/install74.img
#wget https://mirrors.tuna.tsinghua.edu.cn/OpenBSD/7.4/amd64/install74.img  ## a mirror site
## Mount the installer image as the boot disk
lxc config device add n1 install disk source=$(realpath install74.img) boot.priority=10
## Start OpenBSD to install it
lxc start n1 --console
```

Manually configure the correct serial output device, otherwise the OS won't print any output to our attached text console (Tip: enter the `set tty com0` command as quick as possible):

```txt
>> OpenBSD/amd64 BOOTX64 3.65
boot> set tty com0
boot> boot
```

Press `I` and answer the questions presented by the installer:

```txt
Welcome to the OpenBSD/amd64 7.4 installation program.
(I)nstall, (U)pgrade, (A)utoinstall or (S)hell? I
```

Most answers will depend on your personal preference. Usually choosing the default is a good choice. Make sure to change the default console to com0 and pick a reasonable baud rate, start sshd by default, and allow root ssh login.

```txt
System hostname? (short form, e.g. 'foo') sandtable-node
Start sshd(8) by default? [yes]
Change the default console to com0? [yes]
Available speeds are: 9600 19200 38400 57600 115200.
Which speed should com0 use? (or 'done') [9600] 115200
Allow root ssh login? (yes, no, prohibit-password) [no] yes
Location of sets? (disk http nfs or 'done') [disk] disk
Is the disk partition already mounted? [no]
Available disks are: sd0 sd1.
Which disk contains the install media? (or 'done') [sd1]
Directory does not contain SHA256.sig. Continue without verification? [no] yes
```

Once installer is done, we shut down the virtual machine by shell command `halt -p`:

```txt
CONGRATULATIONS! Your OpenBSD install has been successfully completed!

When you login to your new system the first time, please read your mail
using the 'mail' command.

Exit to (S)hell, (H)alt or (R)eboot? [reboot] S
```

Now remove the mounted install image:

```sh
lxc config device remove n1 install
```

Start OpenBSD:

```sh
lxc start n1
```

## Configure Shared Directories

Install SSH and configure SSH root login (inside sandtable-lxc, in this tutorial use `lxc shell sandtable-lxc` to run as root):

```sh
sudo apt-get update
sudo apt-get install -y ssh
echo PermitRootLogin prohibit-password | sudo tee -a /etc/ssh/sshd_config
sudo systemctl restart ssh
```

Generate authentication keys for SSH (inside sandtable-lxc):

```sh
## Run as root
sudo -i
mkdir /root/.ssh
cd /root/.ssh
ssh-keygen -f id_rsa -N "" -C root@sandtable-lxc
install -m 0600 id_rsa.pub authorized_keys
```

Copy sandtable-lxc's authentication keys to OpenBSD (inside sandtable-lxc):

```sh
## Run as root
scp -r /root/.ssh root@n1:/root
```

Now sandtable-lxc and OpenBSD node n1 can SSH to each other. We configure a shared directory for them.

Clone SandTable (on host):

```sh
sudo apt-get install -y git make rsync
git clone https://github.com/tangruize/SandTable.git
cd SandTable
## Copy project files to build/mount
make sync-docker-files
```

Configure shared directory for sandtable-lxc (on host):

```bash
## `shift=true` is required for proper permissions
lxc config device add sandtable-lxc sandtable disk source=$(realpath build/mount) path=/root/sandtable shift=true
```

SSH to OpenBSD (which in this case is `n1.lxd`. If `n1.lxd` cannot be [resolved](https://documentation.ubuntu.com/lxd/en/stable-5.0/howto/network_bridge_resolved/), you can use the IPv4 address instead):

```sh
ssh root@n1.lxd
# If n1.lxd cannot be resolved, use the IPv4 address
ssh root@$(lxc info n1 | sed -En '/inet:/s/.* ([0-9.]+).*/\1/p')
```

Install sshfs for mounting shared directory (on OpenBSD):

```sh
pkg_add sshfs
```

Configure sshfs for auto-mounting (on OpenBSD):

```sh
(crontab -l 2>/dev/null; echo "@reboot /bin/mkdir -p /root/sandtable && /usr/local/bin/sshfs -o allow_other,reconnect,IdentityFile=/root/.ssh/id_rsa root@sandtable-lxc:/root/sandtable /root/sandtable") | crontab -
```

## Build SandTable

Install the essential toolchains for building the SandTable engine (i.e., `src/controller`) (inside sandtable-lxc):

```sh
sudo apt-get update
sudo apt-get install -y cmake build-essential libgflags-dev libreadline-dev libconcurrentqueue-dev
```

Build the engine (inside sandtable-lxc):

```sh
cd /root/sandtable
cmake -B cmake-build-debug/controller -S src/controller
cmake --build cmake-build-debug/controller -j $(nproc)
```

Install the essential toolchains for building the SandTable interceptor (inside OpenBSD):

```sh
pkg_add g++ gcc cmake
```

Build the interceptor (inside OpenBSD):

```sh
cd /root/sandtable
cmake -B cmake-build-debug/interceptor -S src/interceptor
cmake --build cmake-build-debug/interceptor -j $(sysctl hw.ncpu | awk -F= '{print $2}')
```

## Replay Bugs

Install the necessary packages on host:

```sh
sudo apt-get install -y nftables iptables jq
```

Install the packages of the engine defined in [Dockerfile](../docker/Dockerfile) (inside sandtable-lxc):

```sh
sudo apt-get install -y iproute2 iptables ssh dnsutils python3 python-is-python3 python3-pip openjdk-19-jre-headless
sudo apt-get install -y lsof tmux jq
sudo -H pip install jq requests inotify psutil
```

Configure TPROXY (on host):

```sh
make unconfig-network-lxd
make config-network-lxd
```

The dependencies required on each node to run the interceptor depend on the target systems. For example, to run PySyncObj, python3 needs to be installed on OpenBSD:

```sh
pkg_add python3
```

Copy OpenBSD node `n1` to `n2` and `n3` (on host):

```sh
## If the storage backend is DIR, copy operations will be slow
lxc copy n1 n2
lxc copy n1 n3
lxc start n1 n2 n3
```

Reply PySyncObj bugs (execute on host):

```sh
make BACKEND=lxc replay_pysyncobj_leader_commits_older_terms_bug
make BACKEND=lxc replay_pysyncobj_non_monotonic_commit_idx_bug
make BACKEND=lxc replay_pysyncobj_next_idx_no_greater_than_match_idx_bug
make BACKEND=lxc replay_pysyncobj_non_monotonic_match_idx_bug
```

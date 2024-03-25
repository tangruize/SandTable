# Setting Up a Linux Environment

The Linux environment must meet the following requirements: it should be capable of installing snapd (for LXD installation) and have a kernel version of at least 4.18 (to support TPROXY). It is advisable to have a kernel version of at least 5.19 (to support OverlayFS IDMAPPED layers) for Docker to function optimally inside LXD containers.

If you are already using a Linux host, you can skip this tutorial.

## Installing Ubuntu on Host/VirtualBox

Download the Ubuntu 24.04 installer iso or Ubuntu 22.04 iso and install it on a physical or virtual machine (e.g., VirtualBox).

Tip: The graphical installation guide of Ubuntu>=22.04 supports installing the root filesystem on ZFS (Erase disk and use ZFS), which works better with LXD compared to EXT4. For enhanced ZFS functionality, it is recommended to install ZFS>=2.2 (to support ZFS delegation), which is available on Ubuntu 23.10 and 24.04.

## Installing Ubuntu 22.04 on WSL2

Search for Ubuntu on the Microsoft Store and install Ubuntu 22.04.3 LTS.

Currently, the official WSL2 kernel does not have TPROXY configured, and the version is 5.15. To enable TPROXY and improve Docker performance inside LXD, we need to configure and compile the WSL2 kernel.

```bash
git clone https://github.com/microsoft/WSL2-Linux-Kernel.git
cd WSL2-Linux-Kernel
git checkout linux-msft-wsl-6.1.y
cp Microsoft/config-wsl .config
## We do not config ZFS because ZFS does not directly support to run inside a container (due to mount namespaces).
## Linux distributions run as isolated containers inside of the WSL 2 managed VM.
cat <<EOF >>.config
# To support TPROXY
CONFIG_NFT_TPROXY=y
CONFIG_NETFILTER_XT_TARGET_TPROXY=y
CONFIG_NF_TPROXY_IPV4=y
CONFIG_NF_TPROXY_IPV6=y
# Optional configs to support LXD virtual machines (required if we want to try Install-OpenBSD.md)
CONFIG_VIRTIO_VSOCKETS_COMMON=m
CONFIG_VHOST_IOTLB=m
CONFIG_VHOST=m
CONFIG_VHOST_NET=m
CONFIG_VHOST_VSOCK=m
CONFIG_VHOST_VDPA=m
EOF
make -j$(nproc)
make INSTALL_MOD_PATH=$(pwd)/myroot modules_install
tar czf modules.tar.gz -C myroot/lib modules
```

Copy `./arch/x86/boot/bzImage` to Windows and copy `./modules.tar.gz` to Ubuntu 22.04 WSL2.

To configure the WSL2 kernel, edit `%HOMEPATH%/.wslconfig`:

```conf
[wsl2]
kernel=C:\\path\\to\\bzImage
kernelCommandLine = cgroup_no_v1=all  # Optional to run nested LXD containers
nestedVirtualization=true  # Optional to run LXD VMs
## Optional configs below
#localhostforwarding=true
#guiApplications=false
#memory=8GB
#processors=4
```

Configure modules on Ubuntu 22.04 WSL2:

```bash
sudo tar xzf modules.tar.gz -C /lib
sudo depmod -e
```

Ensure that Ubuntu 22.04 WSL2 is booted with systemd (`/etc/wsl.conf`):

```conf
[boot]
systemd=true
```

After configuration, reboot Ubuntu 22.04 WSL2.

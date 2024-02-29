# SandTable: Scalable Distributed System Model Checking with Specification-Level State Exploration

## Overview

SandTable is a technique for lifting state-space exploration of distributed system model checking from the implementation level to the specification level, and confirming bugs at the implementation level.
SandTable has been applied to 8 distributed systems that implement consensus protocols such as Raft and Zab, where it found 23 bugs in total, with 18 new bugs, 17 confirmed and 13 fixed.
For details, please refer to the `SandTable` paper:

**[SandTable: Scalable Distributed System Model Checking with Specification-Level State Exploration](doc/SandTable-Paper.pdf)**<br>
In Proceedings of the 19th European Conference on Computer Systems (EuroSys'24), Athens, Greece, Apr. 2024. <https://doi.org/10.1145/3627703.3650077>

Please cite the paper if you use the code.

## Getting started

Before utilizing SandTable for checking distributed systems, users are required to write the specification of the core protocol. We provide detailed steps on how to use SandTable [here](doc/SandTable-Design.pdf) (in Chinese). We are actively working on simplifying this process to make it more user-friendly.

## Demo

To demonstrate SandTable's bug-finding capabilities, we reproduce one of the new bugs discovered by SandTable. For a detailed installation tutorial, please refer to [Install.md](doc/Install.md). For detailed instructions to reproduce bugs, please see [Reproduce-Bugs.md](doc/Reproduce-Bugs.md). For detailed analysis of bugs, please see [Bugs-Descriptions.pdf](doc/Bugs-Descriptions.pdf) (in Chinese) or its [translated English version](doc/Bugs-Descriptions_EN.pdf).

First, install necessary dependencies on Ubuntu (version >= 20.04):

```sh
sudo apt-get install -y docker.io docker-compose rsync git iptables make jq
```

Then, build and start docker:

```sh
make build-docker && make start-docker
```

To reproduce the multiple valid leader bug in Xraft, execute the following command:

```sh
make replay_xraft_election_safety_bug
```

After replay, it will provide information about the bug, indicating two servers becoming leaders with the same term:

```txt
grep -r "become leader, term" build/mount/systems/Xraft-series/bugs/election_safety/test/log*
build/mount/systems/Xraft-series/bugs/election_safety/test/log.1:2022-06-04 05:36:58.200 [node] INFO  node.NodeImpl - become leader, term 2
build/mount/systems/Xraft-series/bugs/election_safety/test/log.3:2022-06-04 05:36:54.100 [node] INFO  node.NodeImpl - become leader, term 2
```

## Contributing

Thank you for your interest in SandTable! We highly appreciate all feedback and contributions. If you wish to file a bug or enhancement proposal or have other questions, please use the Github [Issue](https://github.com/tangruize/SandTable/issues/new). If you'd like to contribute code, please open a Pull Request.

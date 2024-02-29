FROM ubuntu:22.04 as base

LABEL version="0.1" maintainer="Ruize Tang <1466040111@qq.com>"

# basic packages for running the project
RUN sed -E -i.orig 's,/[a-z]+\.ubuntu\.com,/mirrors.tuna.tsinghua.edu.cn,' /etc/apt/sources.list && \
    apt-get update && \
    apt-get install -y iproute2 iptables ssh dnsutils python3 python-is-python3 python3-pip openjdk-19-jre-headless

# password-free SSH, and keep running scripts
RUN echo 'PermitRootLogin prohibit-password' >> /etc/ssh/sshd_config && \
    mkdir /root/.ssh && cd /root/.ssh && ssh-keygen -f id_rsa -N "" -C root@controller && install -m 0600 id_rsa.pub authorized_keys && \
    echo >> /start.sh 'service ssh restart' && \
    echo >> /start.sh 'test -f /start-user.sh && bash "/start-user.sh"' && \
    echo >> /start.sh 'tail -f /dev/null'  && \
    chmod +x /start.sh

EXPOSE 22

CMD ["bash", "/start.sh"]

# Add more RUNs below

FROM base as tools

# Convenient tools for debugging
RUN apt-get install -y vim git wget curl sudo

FROM tools as node
RUN apt-get install -y libgflags2.2 libreadline8
# Install python3.7 for RaftOS
RUN sudo apt-get install -y software-properties-common
RUN sudo add-apt-repository ppa:deadsnakes/ppa \
    && sudo apt-get update \
    && sudo apt-get install -y python3.7-venv

FROM tools as builder
RUN apt-get install -y cmake build-essential libgflags-dev libreadline-dev libconcurrentqueue-dev

FROM builder as controller
RUN apt-get install -y lsof tmux jq
COPY requirements.txt /requirements.txt
RUN pip install -r /requirements.txt && rm -f /requirements.txt

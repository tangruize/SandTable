//
// Created by tangruize on 22-5-17.
//

#include "TcpNetwork.h"

#include <unistd.h>
#include <thread>
#include <sys/epoll.h>
#include <sys/sendfile.h>
#include <netinet/tcp.h>
#include <chrono>

//DECLARE_bool(deliver_first_msg);
DECLARE_bool(delay_connect);
DECLARE_int32(block_connect_timeout);
DECLARE_int32(merge_small_msg);
DECLARE_bool(dump_msg);
DECLARE_bool(multi_ports);
DECLARE_bool(abort_failed_init);
DECLARE_bool(partition_keep_msgs);
DECLARE_bool(allow_msg_unordered);

#define ROUTER_FD (-2)
#define PENDING_FD (-3)

void TcpNetwork::run_epoll() {
    struct epoll_event events[max_events];
    int nfds, listen_fd = tcp->socket();
    pair<int, int> conn_fds;
    while (true) {
        nfds = epoll_wait(epoll_fd, events, max_events, -1);
        if (nfds == -1) {
            if (errno == EINTR) {
                cerr_detail << "epoll_wait is interrupted by signal" << endl;
                continue;
            }
            else
                throw_syserror("epoll_wait");
        }
        for (int n = 0; n < nfds; ++n) {
            if (events[n].data.fd == listen_fd) {
                while (true) {  // edge trigger, accept until no request to handle
                    conn_fds = do_accept_connect();
                    if (conn_fds.first == ROUTER_FD)
                        continue; // router fd
                    if (conn_fds.first == -1 && conn_fds.second == -1)
                        break; // failed
                    // add_monitor_fd(conn_fds.first);
                    // add_monitor_fd(conn_fds.second);
                    if (conn_fds.first >= 0)
                        add_monitor_fd(conn_fds.first);
                    if (conn_fds.second >= 0)
                        add_monitor_fd(conn_fds.second);
                }
            } else {
                auto it = fd_to_client.find(events[n].data.fd);
                if (it != fd_to_client.end()) {
                    // router <-> client connection
                    if (!check_connection_is_active(it->first)) {
                        // close
                        cerr_verbose << "Close client fd: " << it->first << " "
                                     << configFile.get_node_name_with_addr(it->second) << " <-> "
                                     << configFile.get_node_name_with_addr(configFile.router_addr) << endl;
                        close(it->first);
                        // TODO: (bug) concurrent, should erase carefully
                        client_to_fd.erase(it->second);
                        fd_to_client.erase(it->first);
                    }
                } else {
                    // client <-> client connection
                    do_receive(events[n].data.fd);
                }
            }
        }
    }
}

TcpNetwork::TcpNetwork(TcpSocket *tcp_socket, bool half_duplex) : tcp(tcp_socket) {
    epoll_fd = epoll_create1(0);
    if (epoll_fd == -1)
        throw_syserror("epoll_create1");
    add_monitor_fd(tcp_socket->socket());
    is_direct = configFile.get_strategy() == STRATEGY_DIRECT;
    is_half_duplex = half_duplex;
}

void TcpNetwork::set_recv_timeout(int fd) {
    if (fd == -1)
        return;
    if (setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &recv_timeout, sizeof(recv_timeout)) == -1)
        warn_syserror("set_recv_timeout setsockopt fd: " + to_string(fd));
}

void TcpNetwork::set_conn_retries(int fd) {
    if (setsockopt(fd, IPPROTO_TCP, TCP_SYNCNT, &syn_retries, sizeof(syn_retries)) == -1)
        warn_syserror("set_conn_retries setsockopt fd: " + to_string(fd));
}

int TcpNetwork::connect_peer(const AcceptData &acc) {
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd == -1) {
        warn_syserror("connect_peer socket");
        return -1;
    }
    const int opt = 1;
    // to bind to any addr
    if (setsockopt(fd, SOL_IP, IP_TRANSPARENT, &opt, sizeof(opt)) == -1) {
        warn_syserror("connect_peer setsockopt");
        return -1;
    }
    // to bind to client addr with a random port
    struct sockaddr_in client = acc.origin_client_addr;
    client.sin_port = 0;
    if (bind(fd, (struct sockaddr *)&client, sizeof(client)) == -1) {
        warn_syserror("connect_peer setsockopt");
        return -1;
    }
    set_conn_retries(fd);
    if (FLAGS_block_connect_timeout <= 0) {
        if (connect(fd, (struct sockaddr *)&acc.masque_addr, sizeof(acc.masque_addr)) == -1) {
            sleep(1);  // retry
            if (connect(fd, (struct sockaddr *)&acc.masque_addr, sizeof(acc.masque_addr)) == -1) {
                warn_syserror("connect_peer connect");
                close(fd);
                return -1;
            }
        }
    } else {
        auto end_time = time(NULL) + FLAGS_block_connect_timeout;
        while (connect(fd, (struct sockaddr *)&acc.masque_addr, sizeof(acc.masque_addr)) == -1) {
            auto saved_errno = errno;
            if (time(NULL) > end_time) {
                errno = saved_errno;
                warn_syserror("connect_peer connect");
                close(fd);
                break;
            }
            sleep(1);
        }
    }
    cerr_verbose << "Connected peer fd: " << fd << " " << channel_to_string({acc.masque_addr, acc.client_addr, false})
                 << " (bind: " << configFile.get_node_name_with_addr(acc.origin_client_addr) << ")" << endl;
    return fd;
}

void TcpNetwork::add_fd_to_channel(int src_fd, int dst_fd, const AcceptData& acc) {
    struct sockaddr_in src = acc.client_addr;
    struct sockaddr_in dst = acc.masque_addr;
    if (!FLAGS_multi_ports) {
        src.sin_port = 0;
        dst.sin_port = 0;  // disable multiple ports
    }
    shared_ptr<int> src_fd_ptr(new int{src_fd}), dst_fd_ptr(new int{dst_fd});
    fd_to_channel_status[src_fd] = { .channel = {src, dst, false},
                                     .self_fd = src_fd_ptr, .fd = dst_fd_ptr, .disconnected = false};
    network[{src, dst, false}].deliver_next_msg =
            configFile.check_port_to_deliver_first_msg((short)ntohs(dst.sin_port));
    struct channel_status_t dst_channel = {.channel = {dst, src, is_half_duplex},
                                           .self_fd = dst_fd_ptr, .fd = src_fd_ptr, .disconnected = false};
    if (dst_fd != PENDING_FD) {
        fd_to_channel_status[dst_fd] = dst_channel;
        network[{dst, src, is_half_duplex}];
    } else {
        pending_connections.emplace_back(acc, dst_channel);
    }
}

pair<int, int> TcpNetwork::do_accept_connect() {
    AcceptData acc = tcp->accept();
    if (acc.socket_fd == -1)
        return {-1, -1};  // failed, no more to accept
    if (configFile.is_router_addr(acc.origin_addr)) {
        string node_name = configFile.get_node_name_with_addr(acc.client_addr);
        cerr_verbose << "Client " << configFile.get_node_name_with_addr(acc.client_addr)
                     << " cmd fd: " << acc.socket_fd << endl;
        acc.client_addr.sin_port = 0;
        client_to_fd[acc.client_addr] = acc.socket_fd;
        fd_to_client[acc.socket_fd] = acc.client_addr;
        add_monitor_fd(acc.socket_fd);
        remote_control->add_node(configFile.get_node_name(acc.client_addr), acc.socket_fd);
        return {ROUTER_FD, ROUTER_FD};  // success, is router fd
    }
    int peer_fd = connect_peer(acc);
    if (peer_fd == -1) {
        if (!FLAGS_delay_connect) {
            close(acc.socket_fd);
            return {-1, -1};  // failed
        }
        peer_fd = PENDING_FD;
    }
//    cerr_warning << "set_recv_timeout " << acc.socket_fd << " " << peer_fd << endl;
    set_recv_timeout(acc.socket_fd);
    set_recv_timeout(peer_fd);
    add_fd_to_channel(acc.socket_fd, peer_fd, acc);
    // add_monitor_fd(acc.socket_fd);
    // add_monitor_fd(peer_fd);
    return {acc.socket_fd, peer_fd};
}

void TcpNetwork::add_monitor_fd(int fd) const {
    if (fd < 0)
        return;
    struct epoll_event ev{};
    ev.events = EPOLLIN | EPOLLET;  // edge triggered
    ev.data.fd = fd;
    if (epoll_ctl(epoll_fd, EPOLL_CTL_ADD, fd, &ev) == -1)
        warn_syserror("epoll_ctl");
    else {
//        cerr_warning << "Debug: INTO add_monitor_fd" << endl;
    }
}

void TcpNetwork::enqueue_messages_array(const Msg &msg) {
    messages_array.push_back(msg);
    // cerr_detail << "Enqueue " << messages_array.size() << " fd: " << *msg.fd << endl;
}

void TcpNetwork::do_receive(int fd) {
    MsgHeader header{};
    ssize_t size;
    auto cf = fd_to_channel_status.find(fd);
    if (cf == fd_to_channel_status.end()) {
        cerr_warning << "do_receive cannot find channel of fd: " << fd << endl;
        close_connection(fd);
        return;
    }
    bool is_unintercepted = unintercepted_fd.count(fd);
    if (!unintercepted_fd.count(fd)) {
        while ((size = recv(fd, &header, sizeof(header), MSG_DONTWAIT | MSG_PEEK)) == sizeof(header)) {
            if (!packet_validation(header, size)) {
                // validation failed, tag as not intercepted
                cerr_warning << "do_receive recv validation failed of fd: " << fd << " size: " << size << endl;
                cerr_warning_cont << "- Contents:" << endl;
                cerr_warning_cont << "0x";
                cerr_warning_cont << std::hex << std::setw(8) << std::setfill('0') << ntohl(header.validation)
                                  << std::hex << std::setw(8) << std::setfill('0') << ntohl(header.size)
                                  << std::dec << endl;
                set_unintercepted(fd, cf->second.channel);
                is_unintercepted = true;
                break;
            }
            Msg msg(cf->second.fd, header);
            // header is still in recv queue because we use MSG_PEEK flag
            size = recv(fd, msg.buffer(), sizeof(header) + msg.size, MSG_WAITALL);
            if (size == -1) {
                if (errno != EAGAIN) {
                    warn_syserror("do_receive recv content fd: " + to_string(fd));
                } else {  // connection is closed
                    // Question? close connection immediately?
                    close_connection(fd);
                }
                return;
            } else if ((size_t) size != sizeof(header) + msg.size) {
                cerr_warning << "do_receive recv incomplete content of fd: " << fd
                             << " size: " << size - sizeof(header) << " expected size: " << msg.size << endl;
                // Question? In what condition partial read can happen except EOF?
                // Question? close connection if partial read?
                close_connection(fd);
                return;
            }
            // ok recv 1 msg
//            cerr_warning << "Debug: INTO enqueue_msg" << endl;
            enqueue_msg(cf->second, msg);
        }
        if (size == -1) {
            if (errno != EAGAIN) {  // EAGAIN: no more data to recv
                warn_syserror("do_receive recv header fd: " + to_string(fd));
                close_connection(fd);
            }
        } else if (size == 0) {
            // EOF
            auto it = fd_to_channel_status.find(fd);
            if (it != fd_to_channel_status.end()) {
                cerr_verbose << "Connection read end closed by peer " << it->second.channel << endl;
            } else {
                cerr_verbose << "Connection read end closed by peer fd: " << fd << endl;
            }
            close_connection(fd);
        } else if (!is_unintercepted) {
            cerr_warning << "do_receive recv incomplete header of fd: " << fd << " size: " << size << endl;
            if (!packet_validation(header, size)) {
                set_unintercepted(fd, cf->second.channel);
                is_unintercepted = true;
            } else {
                cerr_warning << "do_receive validation OK?" << endl;
            }
        }
    }
    if (is_unintercepted) {
        transfer_unintercepted(*cf->second.fd, fd);
    }
}

void TcpNetwork::enqueue_msg(const channel_status_t &cf, Msg &m) {
    if (cf.disconnected) {
        cerr_verbose << "Drop disconnected msg " << cf.channel << ": size: " << m.size << endl;
        return;
    }
    if (is_direct) {
        // not to enqueue, deliver direct
        deliver_msg(cf.channel, &m);
        return;
    }
    ChannelMsgs &cm = network[cf.channel];
    if (cm.deliver_next_msg && *cf.fd != PENDING_FD) {
        cm.deliver_next_msg = false;
        cerr_detail << "TcpNetwork::enqueue_msg deliver the first msg" << endl;
        deliver_msg(cf.channel, &m);
        return;
    }
    if (FLAGS_dump_msg) {
        cerr_detail << "Dump msg to enqueue: " << m.to_string() << endl;
    }
    if (FLAGS_allow_msg_unordered) {
        enqueue_messages_array(m);
    }
    if (int(m.size) <= FLAGS_merge_small_msg && cm.wait_merge == NULL) {
        cerr_detail << "Wait merge: in_fd: " << *cf.self_fd << ", out_fd: " << *cf.fd
                    << ", " << cf.channel << " size: " << m.size << endl;
        cm.wait_merge = new Msg(std::move(m));
    } else if (cm.wait_merge != NULL) {
        cm.wait_merge->content += m.content.substr(sizeof(struct MsgHeader));
        cm.wait_merge->size += m.size;
//        cerr << "merge: " << cm.wait_merge->to_string() << endl;
//        cerr << "msg:   " << m.to_string() << endl;
//        cerr << "merge content: " << cm.wait_merge->content << ", length: " << cm.wait_merge->content.length() << endl;
//        cerr << "msg content:   " << m.content << ", length:" << m.content.size() << endl;
        cm.wait_merge->header = (struct MsgHeader *)cm.wait_merge->buffer();
        cm.wait_merge->header->size = htonl(cm.wait_merge->size);
        cerr_detail << "Enqueue merged: in_fd: " << *cf.self_fd << ", out_fd: " << *cf.fd
                    << ", " << cf.channel << " size: " << cm.wait_merge->size << endl;
        cm.msgs.enqueue(std::move(*cm.wait_merge));
        delete cm.wait_merge;
        cm.wait_merge = NULL;
    } else {
        cerr_detail << "Enqueue in_fd: " << *cf.self_fd << ", out_fd: " << *cf.fd
                    << ", " << cf.channel << " size: " << m.size << endl;
        cm.msgs.enqueue(std::move(m));
    }
}

bool TcpNetwork::deliver_msg(const channel_t &c, Msg *m, bool try_deliver) {
    // get msg to deliver
    Msg msg(m);
    channel_t channel{};
    if (!m || FLAGS_allow_msg_unordered) {  // if FLAGS_allow_msg_unordered, just dequeue but still use arg m for delivery
        auto it = network.find(c);
        channel = it->first;
//        assert(it != network.end());
        if (it == network.end()) {
            cerr_warning << "deliver_msg cannot find channel " << channel << endl;
            return false;
        }
//        ChannelMsgs &cm = network[channel];
        int drop_count = -1;
        do {
            bool ok;
            if (FLAGS_allow_msg_unordered) {
                Msg tmp;  // for dropping the message. The dropped one might be a different msg than m.
                          // It is ok because we just drop it to maintain the network buffer count
                ok = it->second.msgs.try_dequeue(tmp);
                if (!ok) {
                    cerr_warning << "deliver_msg cannot find a msg to drop for unordered delivery" << endl;
                }
            } else {
                if (!try_deliver)
                    ok = it->second.msgs.wait_dequeue_timed(msg, deliver_timeout);
                else {
                    ok = it->second.msgs.try_dequeue(msg);
                    if (!ok)
                        return false;
                }
            }
//            bool ok = cm.msgs.wait_dequeue_timed(msg, deliver_timeout);
            drop_count++;
            if (!ok) {
                cerr_warning << "deliver_msg wait_dequeue_timed timeout ";
                if (drop_count) {
                    cerr_warning_cont << "(dropped " << drop_count << " closed msgs) ";
                }
                cerr_warning_cont << channel << endl;
                return false;
            }
        } while (*msg.fd < 0);
        if (drop_count) {
            cerr_verbose << "Drop " << drop_count << " closed connection msgs: " << channel << endl;
        }
    } else {
        channel = c;
    }
    // check channel is connected or not
    auto fd_it = fd_to_channel_status.find(*msg.fd);
    if (fd_it == fd_to_channel_status.end()) {
        cerr_warning << "deliver_msg cannot find channel for fd (msg dropped): " << msg.fd << endl;
        return false;
    } else if (fd_it->second.disconnected) {
        if (!FLAGS_partition_keep_msgs) {
            cerr_warning << "deliver_msg channel is disconnected (msg dropped): " << channel << endl;
            return false;
        } else {
            cerr_verbose << "deliver_msg deliver a partitioned message" << endl;
        }
    }
    // do deliver
    ssize_t left_size = ssize_t(msg.size), size;
    while (left_size > 0 && (size = write(*msg.fd, msg.body(), left_size)) != -1)
        left_size -= size;
    if (size == -1) {
        warn_syserror("deliver_msg write " + channel_to_string(channel));
        close_connection(*msg.fd, !is_direct);  // close connection on write error
        return false;
    }
    cerr_detail << "Deliver msg " << channel << " fd: " << *msg.fd << " size: " << msg.size << endl;
    if (FLAGS_dump_msg) {
        cerr_detail << "  Content: " << msg.to_string() << endl;
    }
    return true;
}

string TcpNetwork::channel_to_string(const channel_t &c) {
    string src = configFile.get_node_name_with_addr(c.first);
    string dst = configFile.get_node_name_with_addr(c.second);
    return src + " -> " + dst + (c.half_duplex_reverse_direction ? " (passive)" : "");
}

void TcpNetwork::close_connection(int fd, bool tag, bool close_peer, bool reopen) {
    string verbose_str = tag ? "Tag disconnected " : "Close connection ";
    if (tag && reopen) {
        verbose_str = "Tag connected ";
    }
    auto it = fd_to_channel_status.find(fd), it2 = it;
    bool flag = reopen ? false : true;
    if (it != fd_to_channel_status.end()) {
        cerr_verbose << verbose_str << "fd: " << fd << " " << it->second.channel << endl;
        it->second.disconnected = flag;
//        clear_msgs(it->second.channel);
        it2 = fd_to_channel_status.find(*it->second.fd);
        if (it2 != fd_to_channel_status.end()) {
            if (!close_peer)
                verbose_str = "Tag disconnected ";
            cerr_verbose << verbose_str << "(reverse) " << "fd: " << it2->first << " " << it2->second.channel << endl;
            it2->second.disconnected = flag;
//            clear_msgs(it2->second.channel);
        }
        if (!reopen && !tag) {
            do_close(it);
            if (close_peer)
                do_close(it2);
        }
    } else {
        if (!reopen && !tag) {
            cerr_verbose << "Close connection fd: " << fd << endl;
            close(fd);
        }
    }
}

void TcpNetwork::do_close(map<int, channel_status_t>::iterator it) {
    // TODO: (bug) concurrent, should erase carefully
    if (it == fd_to_channel_status.end()) {
        return;
    }
    auto ui_it = unintercepted_fd.find((it->first));
    if (ui_it != unintercepted_fd.end())
        unintercepted_fd.erase(ui_it);
    auto net_it = network.find(it->second.channel);
    if (net_it != network.end())
        network.erase(net_it);
    close(it->first);
    *it->second.self_fd = -1;
    fd_to_channel_status.erase(it);
}

bool TcpNetwork::packet_validation(const MsgHeader &header, unsigned size) const {
    unsigned mask = -1;
    if (size < 4)
        mask >>= (4 - size) * 8;
    return (ntohl(header.validation) & mask) == (VALIDATION_DATA & mask);
}

void TcpNetwork::set_unintercepted(int fd, const channel_t &channel) {
    if (!unintercepted_fd.count(fd)) {
        cerr_verbose << "Unintercept fd: " << fd << " " << channel << endl;
        unintercepted_fd.insert(fd);
//        set_nonblocking(fd);
    }
}

void TcpNetwork::transfer_unintercepted(int out_fd, int in_fd) {
    uint8_t buffer[1460];  // MSS: 1500(MTU)-20(IP)-20(TCP)
    ssize_t size, total = 0;
    while ((size = recv(in_fd, buffer, sizeof(buffer), MSG_DONTWAIT)) > 0) {
        if (send(out_fd, buffer, size, MSG_DONTWAIT) == -1) {
            warn_syserror("transfer_unintercepted send");
//            if (errno == EAGAIN)
//                break;
            close_connection(in_fd);
            break;
        }
        total += size;
    }
    if (FLAGS_detail && total) {
        auto it = fd_to_channel_status.find(in_fd);
        if (it != fd_to_channel_status.end()) {
            cerr_detail << "Transfer unintercepted in_fd: " << in_fd << ", out_fd: " << out_fd
                        << ", " << it->second.channel << " size: " << total << endl;
            auto it2 = network.find(it->second.channel);
            if (it2 != network.end() && it2->second.deliver_next_msg) {
                unintercepted_fd.erase(in_fd);  // first msg is not intercepted
                it2->second.deliver_next_msg = false;
                cerr_detail_cont << "- Reintercepted" << endl;
            }
        }
        else {
            cerr_detail << "Transfer unintercepted in_fd: " << in_fd << " -> out_fd: " << out_fd
                        << " size: " << total << endl;
        }
    }
    if (size == -1 && errno != EAGAIN) {
        warn_syserror("transfer_unintercepted recv");
        close_connection(in_fd);
    } else if (size == 0) {  // EOF
        auto it = fd_to_channel_status.find(in_fd);
        if (it != fd_to_channel_status.end()) {
            cerr_verbose << "Unintercepted connection read end closed by peer " << it->second.channel << endl;
        } else {
            cerr_verbose << "Unintercepted connection read end closed by peer in_fd: "
                         << in_fd << " -> out_fd: " << out_fd << endl;
        }
        close_connection(in_fd);
    }
}

void TcpNetwork::print_status() {
    bool showed = false;
    for (auto &i: client_to_fd) {
        cerr << "FD: " << i.second << ", " << configFile.get_node_name_with_addr(i.first)
             << " <-> " << configFile.get_node_name_with_addr(configFile.router_addr) << endl;
        showed = true;
    }
    map<string, map<string, size_t>> msgs_count;
    net_status_cache.clear();
    for (auto &i: fd_to_channel_status) {
        size_t msgs_size = network[i.second.channel].msgs.size_approx();
        cerr << "FD: " << i.first << ", " << i.second.channel << ", "
             << (i.second.disconnected ? "disconnected" : "connnected")
             << ", msgs: " << msgs_size;
//        if (is_half_duplex) {
//            cerr << (i.second.channel.half_duplex_reverse_direction ? ", passive" : ", active");
//        }
        cerr << endl;
        string src = configFile.get_node_name(i.second.channel.first);
        string dst = configFile.get_node_name(i.second.channel.second);
        msgs_count[src][dst] += msgs_size;
        showed = true;
    }
    for (auto &i: msgs_count) {
        net_status_cache += "msgs " + i.first + ":";
        for (auto &j: i.second) {
            net_status_cache += " " + j.first + "(" + to_string(j.second) + ")";
        }
        net_status_cache += "\n";
    }
    cerr << net_status_cache;
//    for (auto &i: network) {
//        cerr << "Network: " << i.first << ", msgs: " << i.second.msgs.size_approx();
//        if (is_half_duplex) {
//            cerr << (i.first.half_duplex_reverse_direction ? ", passive" : ", active");
//        }
//        cerr << endl;
//    }
    if (!showed)
        cerr << "(empty network buffer)" << endl;
}

void TcpNetwork::clear_msgs(const channel_t &channel) {
    auto it = network.find(channel);
    if (it != network.end()) {
        int count = 0;
        for (Msg tmp; it->second.msgs.try_dequeue(tmp); count++);
        if (count) {
            cerr_detail << "Clear " << count << " msgs " << channel << endl;
        }
    }
}

void TcpNetwork::partition(const string &node, bool clear_msg, bool is_recover) {
    struct sockaddr_in addr = configFile.get_node_addr(node);
    if (addr.sin_port == (in_port_t)-1) {
        if (is_recover)
            cerr_warning << "recover ";
        else
            cerr_warning << "partition ";
        cerr_warning_cont << "cannot find node: \"" << node << "\"" << endl;
        return;
    }
    cmp_addr_no_port_equal cmp;
    vector<int> fd_to_close;
    bool matched = false;
    for (auto & it : fd_to_channel_status) {
        if (cmp(it.second.channel.first, addr)) {
            matched = true;
            if (is_recover) {
                it.second.disconnected = false;
                // close fd will delete it from fd_to_channel_status, which corrupt the loop, close it afterwards
                fd_to_close.push_back(it.first);
            }
            else
                close_connection(it.first, true);
            if (clear_msg)
                clear_msgs(it.second.channel);
        }
    }
    for (auto i: fd_to_close) {
        if (clear_msg)
            close_connection(i, false);
        else
            close_connection(i, true, true, true);
    }
    if (!matched) {
        cerr_warning << "No matched channel for node: " << configFile.get_node_name_with_addr(addr) << endl;
    }
}

void TcpNetwork::recover(const string &node) {
        partition(node, true, true);
//    if (servers_count != 0) {
//        connections_to_wait += servers_count - 1;
//    }
}

void TcpNetwork::recover_no_disconnect(const string &node) {
    partition(node, false, true);
}

string TcpNetwork::convert_cmd_check_has_recv_queue(__attribute_maybe_unused__ const string &node, const string &c) {
    // TODO: when multi_ports enabled, convert check_has_recv_queue address/node_name to the real address with port.
    return c;
}

bool TcpNetwork::send_cmd(const string &node, const string &c, int lineno) {
    string cmd;
    if (FLAGS_multi_ports && c.starts_with("check_has_recv_queue")) {
        cmd = convert_cmd_check_has_recv_queue(node, c);
    } else {
        cmd = c;
    }
    struct sockaddr_in addr = configFile.get_node_addr(node);
    cerr_detail << "Send cmd to " << configFile.get_node_name_with_addr(addr) << ": " << cmd << endl;
    int ret = remote_control->send_cmd_interceptor(node, cmd, lineno);
    if (ret < 0) {
        auto it = client_to_fd.find(addr);
        it = client_to_fd.find(addr);
        if (it == client_to_fd.end()) {
            cerr_warning << "send_cmd cannot find client-router connection: \""
                         << configFile.get_node_name_with_addr(addr) << "\"" << endl;
            return false;
        }
        close(it->second);
        // TODO: (bug) concurrent, should erase carefully
        fd_to_client.erase(it->second);
        client_to_fd.erase(it);
    }
    return ret == 0;
}

bool TcpNetwork::check_connection_is_active(int fd) {
    char data;
    ssize_t size = recv(fd, &data, 1, MSG_PEEK | MSG_DONTWAIT);
    if (size == 0 || (size == -1 && errno != EAGAIN))
        return false;
    return true;
//    int error_code;
//    socklen_t size = sizeof(error_code);
//    if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &error_code, &size) == -1) {
//        warn_syserror("check_connection_is_active getsockopt");
//    }
//    return error_code == 0;
}

void TcpNetwork::print_connection_buffer(int fd, bool consume) {
    char data[80] = {0};
    int flags = MSG_DONTWAIT;
    if (consume)
        flags |= MSG_PEEK;
    ssize_t size = recv(fd, data, 79, flags);
    if (size == 0 || (size == -1 && errno == EAGAIN)) {
        cerr_verbose << "No data, returns " << size << endl;
    } else if (size == -1) {
        warn_syserror("print_connection_buffer: fd: " + to_string(fd));
    } else {
        cerr_verbose << "Got size: " << size << ", data: " << data << endl;
    }
}

void TcpNetwork::wait_init(int n_servers, bool double_connections, int wait_ms) {
    int conn_to_wait = 1;
    for (int i = 2; i <= n_servers; i++)
        conn_to_wait = conn_to_wait * i;
    if (double_connections)
        conn_to_wait *= 2;
    cerr_verbose << "Waiting for " << n_servers << " (" << conn_to_wait << " connections)" << endl;

    int i;
    int conn_count = 0;
    int times = wait_ms / 100;
    for (i = 0; i < times; i++) {
        conn_count = 0;
        for (auto &j: fd_to_channel_status) {
            if (!j.second.disconnected) {
                conn_count++;
            }
        }
        if (conn_count == conn_to_wait)
            break;
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        if (i % 10 == 9) {
            cerr_detail << "Current connections: " << conn_count << "/" << conn_to_wait << endl;
        }
    }
    if (i == times && conn_to_wait != conn_count) {
        cerr_warning << "Wait timeout, Connected " << conn_count << "/" << conn_to_wait << " (maybe inaccurate)" << endl;
        if (FLAGS_abort_failed_init) {
            assert(conn_to_wait == conn_count);
        }
    } else {
        cerr_detail << "Connected " << n_servers << " servers, " << conn_count << "/" << conn_to_wait << " connections" << endl;
    }
}

bool TcpNetwork::deliver(const string &from, const string &to, bool all, unsigned seq) {
    channel_t channel{}, channel2{};
    channel.first = channel2.first = configFile.get_node_addr(from);
    channel.second = channel2.second = configFile.get_node_addr(to);
    channel2.first.sin_port = channel2.second.sin_port;
    channel2.second.sin_port = 0;
    channel2.half_duplex_reverse_direction = true;
    if (!channel.ok()) {
        return false;
    }
    do {
        auto it = network.find(channel);
        bool empty_msgs = false;
        if (is_half_duplex && channel2.ok()) {
            auto it2 = network.find(channel2);
            if (it2 != network.end()) {
                if (it == network.end()) {
                    cerr_detail << "Active connection is not found, trying passive connection" << endl;
//                channel.half_duplex_reverse_direction = true;
                    channel = channel2;
                    empty_msgs = it2->second.msgs.size_approx() == 0;
                } else {
                    if (it->second.msgs.size_approx() == 0) {
                        if (it2->second.msgs.size_approx() != 0) {
                            cerr_detail << "Active connection msgs are empty, trying passive connection" << endl;
//                        channel.half_duplex_reverse_direction = true;
                            channel = channel2;
                        } else {
                            empty_msgs = true;
                        }
                    }
                }
            }
        } else if (it != network.end()) {
            empty_msgs = it->second.msgs.size_approx() == 0;
        }
        if (!channel.half_duplex_reverse_direction && it == network.end()) {
            cerr_warning << "deliver cannot find channel: " << channel << endl;
            return false;
        } else if (empty_msgs) {
            if (all)
                return true;
            cerr_warning << "deliver may block due to no message in the channel: " << channel << endl;
            return false;
        }
        if (seq == 0) {
            if (!deliver_msg(channel) && all) {
                return false;
            }
        } else {
            if (seq > messages_array.size()) {
                cerr_warning << "Unordered deliver out of boundary, size: " << messages_array.size() << ", seq: " << seq << endl;
                return false;
            }
            if (!deliver_msg(channel, &messages_array[seq-1])) {
                return false;
            }
        }
    } while (all);
    return true;
}

bool TcpNetwork::deliver_unordered(const string &from, const string &to, unsigned seq) {
    return deliver(from, to, false, seq);
}

void TcpNetwork::wait_recover() {
    wait_init(server_count, is_half_duplex, 5000);
}

void TcpNetwork::deliver_all(int least_count) {
    int count = 0;
    while (true) {
        for (auto &i: network) {
            while (deliver_msg(i.first, nullptr, least_count))
                count++;
        }
        if (count >= least_count)
            break;
        cerr_detail << "TcpNetwork::deliver_all delivered " << count << " msgs" << endl;
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
    }
}

void TcpNetwork::connect_pending() {
    auto it = pending_connections.begin();
    while (it != pending_connections.end()) {
        int peer_fd = connect_peer(it->first);
        if (peer_fd == -1) {
            cerr_warning << "Cannot connect peer "
                         << channel_to_string({it->first.masque_addr, it->first.client_addr, false})
                         << endl;
            it++;
            continue;
        }
        set_recv_timeout(peer_fd);
        add_monitor_fd(peer_fd);
        fd_to_channel_status[peer_fd] = it->second;
        network[it->second.channel];
        *(it->second.fd) = peer_fd;
        cerr_verbose << "Connected peer: " << channel_to_string({it->first.masque_addr, it->first.client_addr, false}) << endl;
        channel_t reverse = {it->second.channel.second, it->second.channel.first, false};
        auto it2 = network.find(reverse);
        if (it2 != network.end()) {
            if (it2->second.deliver_next_msg) {
                if (deliver_msg(reverse, NULL, true)) {
                    cerr_detail << "Delivered first msg" << endl;
                    it2->second.deliver_next_msg = false;
                } else {
                    cerr_warning << "Failed to deliver first msg" << endl;
                }
            }
        }
        it = pending_connections.erase(it);
    }
}

void TcpNetwork::init(int n_servers, int wait_ms) {
    server_count = n_servers;
    cerr_verbose << "Waiting for " << n_servers << " clients" << endl;
    int times = wait_ms / 100;
    int i;
    for (i = 0; i < times; i++) {
        if (int(client_to_fd.size()) == server_count) {
            break;
        }
        std::this_thread::sleep_for(std::chrono::milliseconds(100));
        if (i % 10 == 9) {
            cerr_detail << "Current ready " << client_to_fd.size() << " clients" << endl;
        }
    }
    if (i == times && int(client_to_fd.size()) != server_count) {
        cerr_warning << "Init " << n_servers << " failed after " << wait_ms << "ms timeout" << endl;
        if (FLAGS_abort_failed_init) {
            assert(int(client_to_fd.size()) == server_count);
        }
    } else {
        cerr_detail << "Ready " << n_servers << " clients" << endl;
    }
}

string TcpNetwork::get_status_cache() {
    return net_status_cache;
}

int TcpNetwork::get_net_len() {
    int msgs_count = 0;
    for (auto &i: fd_to_channel_status) {
        int msgs_size = (int)network[i.second.channel].msgs.size_approx();
        msgs_count += msgs_size;
    }
    return msgs_count;
}

// should use carefully due to concurrent
void TcpNetwork::close_client(const string &node) {
    struct sockaddr_in addr = configFile.get_node_addr(node);
    auto it = client_to_fd.find(addr);
    if (it != client_to_fd.end()) {
        int fd = it->second;
        close(fd);
        fd_to_client.erase(fd);
        client_to_fd.erase(it);
        cerr_detail << "Client erased, fd: "  << fd << ", addr: " << configFile.get_node_name_with_addr(addr) << endl;
    } else {
        cerr_warning << "Cannot find client: " << node << endl;
    }
}

void TcpNetwork::pre_close_client(const string &node) {
    struct sockaddr_in addr = configFile.get_node_addr(node);
    auto it = client_to_fd.find(addr);
    if (it != client_to_fd.end()) {
        int fd = it->second;
        del_monitor_fd(fd);
        print_connection_buffer(fd, true);
        cerr_verbose << "Removed from monitor, fd: " << fd << endl;
    } else {
        cerr_warning << "Cannot find client: " << node << endl;
    }
}

void TcpNetwork::del_monitor_fd(int fd) const {
    if (fd < 0)
        return;
    if (epoll_ctl(epoll_fd, EPOLL_CTL_DEL, fd, NULL) == -1)
        warn_syserror("epoll_ctl");
}

bool TcpNetwork::check_client_online(const string &node) {
    struct sockaddr_in addr = configFile.get_node_addr(node);
    auto it = client_to_fd.find(addr);
    if (it == client_to_fd.end())
        return false;
    return true;
}

bool TcpNetwork::send_cmd_all(const string &prefix, const string &cmd, int lineno) {
    bool ok = false;
    cerr_detail << "Send cmd (" << prefix << " " << cmd << ") to all" << endl;
    for (auto &i: client_to_fd) {
        string node = configFile.get_node_name(i.first, false);
        if (!node.empty()) {
            string full_cmd = prefix;
            full_cmd += " ";
            full_cmd += cmd;
            if (0 == remote_control->send_cmd_interceptor(node, full_cmd, lineno))
                ok = true;
        }
    }
    return ok;
}

void TcpNetwork::clear_channel_msgs(const string &from, const string &to) {
    channel_t channel{}, channel2{};
    channel.first = channel2.first = configFile.get_node_addr(from);
    channel.second = channel2.second = configFile.get_node_addr(to);
    channel2.first.sin_port = channel2.second.sin_port;
    channel2.second.sin_port = 0;
    channel2.half_duplex_reverse_direction = true;
    vector<channel_t> channels = {channel, channel2};
    if (!channel.ok()) {
        return;
    }
    for (auto &c: channels) {
        if (!c.ok())
            continue;
        clear_msgs(c);
    }
}

std::ostream &operator<<(ostream &os, const channel_t &channel) {
    os << TcpNetwork::channel_to_string(channel);
    return os;
}

TcpNetwork *net;

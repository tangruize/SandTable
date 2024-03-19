//
// Created by tangruize on 22-5-17.
//

#ifndef TPROXY_UDPNETWORK_H
#define TPROXY_UDPNETWORK_H

#include "common.h"
#include "UdpSocket.h"
#include "Command.h"
#include "Msg.h"
#include "RemoteControl.h"
#include <ctime>
#include <set>
#include <thread>
#include <memory>

//#include <readerwriterqueue.h>
#include <concurrentqueue/blockingconcurrentqueue.h>
using namespace moodycamel;


class UdpNetwork {
private:
    int server_count = 0;
    map<struct sockaddr_in, int, cmp_addr_less> client_to_fd;
    map<int, struct sockaddr_in> fd_to_client;
public:
    string net_status_cache;
    string get_status_cache(){ return net_status_cache;}
    std::thread run_epoll_background() { return std::thread( [this] { this->run_epoll(); }); }
    bool send_cmd(const string &node, const string &cmd, int lineno) ;
    void init(int n_servers);
    bool send_cmd_all(const string &prefix, const string &cmd, int lineno);
private:
    UdpSokcet *udp;
    // seq -> message, 便于定位数据包
    map<int, UdpMsg> network;
    int epoll_fd;
    bool is_direct;
    const int max_events = 10;
    uint32_t msg_counter = 0;
    // for block
    bool flag_block;
    int ssh_fd;
    bool simple_redirect = false;
private:
    void ssh_handle(int tcp_fd);
    int connect_peer(const AcceptData &acc);
    void add_msg_to_net(const AcceptData &client, char* data);
    bool do_send(const uint32_t seq_num);
    bool do_send(const UdpMsg& msg);
    int wait_message(AcceptData* ret, const int udp_socket, char *data) const;
    void add_monitor_fd(int fd) const;
    void add_msg_to_net( AcceptData &client, char* data);
    void add_msg_to_net(sockaddr_in* src, sockaddr_in* dst, char* data);
    void add_msg_to_net(int msg_num, sockaddr_in* src, sockaddr_in* dst, char* data);
    void close_connection(int fd, bool tag_disconnected=false, bool close_peer=true);
    bool packet_validation(const MsgHeader &header, unsigned size) const;
    void transfer_unintercepted(int out_fd, int in_fd);
    static bool check_connection_is_active(int fd);
    int send_to_transparenty(const char *buf,int len,const struct sockaddr_in *source,const struct sockaddr_in *destination);

public:
   public:
    bool deliver(int msg_num) ;
    void print_status();
    void deliver_all(int least_count=0); 
    bool sendData(const string &src, const string &dst, char* data);
    bool dropMessage(int msg_num);
    bool duplicateMessage(int msg_num);
    // set block message into net, but don't send
    void set_block();
    void set_unblock();
public:
    explicit UdpNetwork(UdpSokcet *Udp_socket);
    void run_epoll();
    virtual ~UdpNetwork() {};
};

extern UdpNetwork* udpNet;

#endif //TPROXY_UDPNETWORK_H

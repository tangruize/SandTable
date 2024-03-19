//
// Created by tangruize on 10/12/22.
//

#ifndef TPROXY_REMOTECONTROL_H
#define TPROXY_REMOTECONTROL_H

#include "common.h"
#include <time.h>

class RemoteControl {
private:
    map<string, int> router_to_interceptor;
    map<string, int> router_to_ssh;  // append only
    string tmpdir;
    int do_send(int fd, const string &cmd);
    bool recv_ack(const string &node);
    int get_node_idx(const string &node) const;
    string cache_cmp_data;
    string convert_special_char(const string &cmd);
public:
    RemoteControl();
    ~RemoteControl();
    int add_node(const string &node);
    int add_node(const string &node, int interceptor_fd);
    int try_add_node(double timeout);
    int send_cmd_interceptor(const string &node, const string &cmd, int lineno);
    bool send_cmd_ssh(const string &node, const string &cmd);
    bool send_cmd_ssh_asy(const string &node, const string &cmd);
    string get_cache_cmp_data() const {
        return cache_cmp_data;
    }
    void clear_cache_cmp_data() {
        cache_cmp_data.clear();
    }
};

extern RemoteControl *remote_control;


#endif //TPROXY_REMOTECONTROL_H

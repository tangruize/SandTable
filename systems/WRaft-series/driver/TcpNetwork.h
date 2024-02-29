//
// Created by tangruize on 2/23/23.
//

#ifndef REDISTMET_TCPNETWORK_H
#define REDISTMET_TCPNETWORK_H

#include "common.h"
#include "Network.h"

class TcpNetwork: public Network {
private:
    socklen_t addrlen;
public:
    explicit TcpNetwork(bool run_accept=true);
    int accept();
    void accept_loop();
    void accept_in_background();
    static bool is_connected(int fd);
    bool connect(const Node &n) override;
    void connect_all() override;
    bool is_all_connected() override;
    ssize_t send_to(const Node &peer, const string &data) override;
    ssize_t recv_from(const Node &peer, string &data) override;
};


#endif //REDISTMET_TCPNETWORK_H

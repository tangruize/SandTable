//
// Created by tangruize on 10/12/22.
//

#include "Msg.h"

Msg &Msg::operator=(Msg &&m) noexcept {  // move assign
    fd = std::move(m.fd);
    content = std::move(m.content);
    size = m.size;
    header = (struct MsgHeader *)buffer();
    m.size = 0;
    m.header = nullptr;
    return *this;
}

Msg::Msg(const shared_ptr<int> &sockfd, const MsgHeader &h) {
    fd = sockfd;
    size = ntohl(h.size);
    content.resize(size + sizeof(struct MsgHeader));
    header = (struct MsgHeader *)buffer();
    *header = h;
}

UdpMsg::UdpMsg(uint32_t seq, char* content, struct sockaddr_in* src, struct sockaddr_in* dst){
        this -> sequential = seq;
        this -> content = content;
        this -> src = src;
        this -> dst = dst;
    }

UdpMsg::UdpMsg(const UdpMsg& udpmsg)  {
    this -> sequential = udpmsg.sequential;
    this -> content = udpmsg.content;
    this -> src = udpmsg.src;
    this -> dst = udpmsg.dst;
}

void UdpMsg::set_seq(int seq)  {
    this -> sequential = seq;
}

void UdpMsg::show() const {
    cerr << sequential << " : " << content << " " 
    << configFile.get_node_name_with_addr(*src) << " -> "<< configFile.get_node_name_with_addr(*dst)<<endl;
}
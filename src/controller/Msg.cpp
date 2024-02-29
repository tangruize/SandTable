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

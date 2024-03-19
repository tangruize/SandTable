//
// Created by tangruize on 10/12/22.
//

#ifndef TPROXY_MSG_H
#define TPROXY_MSG_H

#include "common.h"
#include <iomanip>

struct __attribute__((__packed__))  // packed to recv network packet
MsgHeader {
    uint32_t validation;     // validation
    uint32_t size;         // msg length
};

#define VALIDATION_DATA 0xdeadbeef

struct Msg {
    shared_ptr<int> fd;  // each msg has a fd because a channel may have several connections
    struct MsgHeader *header = nullptr;  // caution to use header! it is network endian and is not converted
    string content;
    uint32_t size = 0;
    // Msg(const Msg&) = delete;  // no copy constructor
    explicit Msg(const Msg& m) {  // fpr backward compatibility
        fd = m.fd;
        content = m.content;
        size = m.size;
        header = (struct MsgHeader *)&content;
    }
    Msg& operator=(const Msg &m) = delete;  // no copy assignment
    explicit Msg(Msg *m = nullptr) {
        if (m)
            *this = std::move(*m);
    }
    Msg& operator=(Msg &&m) noexcept;
    Msg(const shared_ptr<int> &sockfd, const struct MsgHeader &h);
    Msg(Msg &&m) noexcept {  // move constructor
        *this = std::move(m);
    }
    char *buffer() {  // buffer pointer
        return &content.front();
    }
    char *body() {  // msg body
        return &content[sizeof(struct MsgHeader)];
    }
    const char *buffer() const {
        return &content.front();
    }
    const char *body() const {
        return &content[sizeof(struct MsgHeader)];
    }
    string to_string() const {
        ostringstream oss;
        oss << std::hex << std::setfill('0');
        const char *b = body();
        for (size_t i = 0; i < size; i++) {
            oss << std::setw(2) << static_cast<unsigned>(b[i]);
        }
        return oss.str();
    }
};

class UdpMsg{
private:
    uint32_t sequential;
    string content;
    struct sockaddr_in* src;
    struct sockaddr_in* dst;
public:
    UdpMsg(uint32_t seq, char* content, struct sockaddr_in* src, struct sockaddr_in* dst);
    UdpMsg(const UdpMsg&udpmsg);  // no copy constructor
    UdpMsg& operator=(Msg &&m) noexcept;
    char *buffer() {  // buffer pointer
        return &content.front();
    }
    const char *buffer() const {
        return &content.front();
    }
    int get_seq() const{
        return sequential;
    }
    int size() const {
        return content.size();
    }
    struct sockaddr_in* get_src() const {
        return src;
    }
    struct sockaddr_in* get_dst() const {
        return dst;
    }
    void set_seq(int seq);
    void show() const;
    
};

#endif //TPROXY_MSG_H

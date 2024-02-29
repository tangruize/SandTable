//
// Created by tangruize on 2/14/23.
//

#include "common.h"

string info_str = "[INFO] ";
string warn_str = "[WARN] ";
string detl_str = "[DETL] ";

// convert ADDR (format: xxx.xxx.xxx.xxx:port)
struct sockaddr_in convert_addr(const char *addr, char delim) {
    struct sockaddr_in res{};
    stringstream ss(addr);
    string ip, port;
    getline(ss, ip, delim);
    getline(ss, port, delim);
    inet_aton(ip.c_str(), &res.sin_addr);
    if (!port.empty()) {
        if (delim == ':')
            res.sin_port = htons(stoi(port));
        else {
            res.sin_port = stoi(port);
            unsigned mask = unsigned(-1) << (32 - res.sin_port);
            res.sin_addr.s_addr = htonl(ntohl(res.sin_addr.s_addr) & mask);
        };
    } else {
        res.sin_port = (in_port_t)-1;
    }
    return res;
}

void init_prompt_color() {
    if (isatty(STDERR_FILENO) && !info_str.empty() && info_str[0] != '\033') {
        info_str = "\033[1;32m" + info_str + "\033[0m";  // bold green
        warn_str = "\033[1;31m" + warn_str + "\033[0m";  // bold red
        detl_str = "\033[1;34m" + detl_str + "\033[0m";  // bold blue
    }
}

vector<string> tokenize(const string &s) {
    vector<string> tokens;
    string token;
    istringstream ss(s);
    while (getline(ss, token, ' ')) {
        if (token.empty())
            continue;
        tokens.push_back(token);
    }
    return tokens;
}

string stringify(const vector<string> &t, size_t start, const string &delim) {
    string result;
    for (size_t i = 0; i < t.size(); i++) {
        if (i > start)
            result += delim + t[i];
        else if (i == start)
            result += t[i];
    }
    return result;
}

bool cmp_addr_less::operator()(const sockaddr_in &a, const sockaddr_in &b) const {
    if (a.sin_addr.s_addr == b.sin_addr.s_addr)
        return a.sin_port < b.sin_port;
    return a.sin_addr.s_addr < b.sin_addr.s_addr;
}

bool cmp_addr_equal::operator()(const sockaddr_in &a, const sockaddr_in &b) const {
//    return a.sin_addr.s_addr == b.sin_addr.s_addr && a.sin_port == b.sin_port;
    return a.sin_addr.s_addr == b.sin_addr.s_addr;
}

bool cmp_addr_no_port_less::operator()(const sockaddr_in &a, const sockaddr_in &b) const {
//    if (a.sin_addr.s_addr == b.sin_addr.s_addr)
//        if (a.sin_port != (in_port_t)-1 && b.sin_port != (in_port_t)-1)
//            return a.sin_port < b.sin_port;
    return a.sin_addr.s_addr < b.sin_addr.s_addr;
}

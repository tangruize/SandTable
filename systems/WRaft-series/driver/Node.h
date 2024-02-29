//
// Created by tangruize on 2/21/23.
//

#ifndef REDISTMET_NODE_H
#define REDISTMET_NODE_H

#include <string>
#include <arpa/inet.h>
#include <algorithm>
#include "common.h"

using namespace std;

#define NODE_PREFIX "n"

struct Node {
    string name;
    struct sockaddr_in addr;
    int id = -1;
    void *data = nullptr;
    Node() = default;
    Node(string name_, const struct sockaddr_in &addr_): name{std::move(name_)}, addr{addr_} { getid(); }
    Node(string name_): name{std::move(name_)}, addr{} { getid(); }
    Node(const struct sockaddr_in &addr_): addr{addr_} {}
    Node(int id_): addr{}, id{id_} { name = NODE_PREFIX + std::to_string(id); }
    bool operator<(const struct Node& b) const;  // less
    bool operator<(const string& b) const;
    bool operator<(const struct sockaddr_in& b) const;
    [[nodiscard]] string gethost() const;
    [[nodiscard]] string getport() const;
    [[nodiscard]] string to_string() const;
    int getid();
    void set_data(void *d) { data = d; }
    [[nodiscard]] void* get_data() const { return data; }
};

#endif //REDISTMET_NODE_H

//
// Created by tangruize on 2/21/23.
//

#include <algorithm>
#include "common.h"
#include "Node.h"


bool Node::operator<(const Node &b) const {
//    if (!name.empty() && !b.name.empty()) {
//        return *this < b.name;
//    } else {
//        return *this < b.addr;
//    }
    return *this < b.name;
}

bool Node::operator<(const string &b) const {
    return name < b;
}

bool Node::operator<(const sockaddr_in &b) const {
    const static cmp_addr_no_port_less al;
    return al(addr, b);
}

string Node::gethost() const {
    return inet_ntoa(addr.sin_addr);
}

string Node::getport() const {
    return std::to_string(ntohs(addr.sin_port));
}

string Node::to_string() const {
    if (!name.empty() && addr.sin_addr.s_addr != 0)
        return "(" + name + ", " + gethost() + ":" + getport() + ")";
    else if (name.empty())
        return "(?UNKNOWN?, " + gethost() + ":" + getport() + ")";
    else
        return "(" + name + ", ?UNKNOWN?)";
}

int Node::getid() {
    if (id < 0) {
        if (name.empty()) {
            cerr_warning << "getid name is empty" << endl;
            return id;
        }
        for (unsigned i = 0; i < name.size(); i++) {
            if ('0' <= name[i] && name[i] <= '9') {
                if (name.substr(0, i) != NODE_PREFIX) {
                    cerr_warning << "node name prefix is not \"" << NODE_PREFIX << "\"" << endl;
                }
                id = stoi(name.substr(i));
                break;
            }
        }
        if (id < 0) {
            cerr_warning << "cannot get node id" << endl;
        }
    }
    return id;
}

//
// Created by tangruize on 2/14/23.
//

#ifndef REDISTMET_COMMON_H
#define REDISTMET_COMMON_H

#include <string>
#include <map>
#include <set>
#include <vector>
#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <gflags/gflags.h>
#include <arpa/inet.h>
#include <unistd.h>

//#include "Config.h"

using namespace std;
using namespace gflags;

extern string info_str;
extern string warn_str;
extern string detl_str;

DECLARE_bool(verbose);
DECLARE_bool(detail);
DECLARE_string(name);

#define cerr_verbose if (FLAGS_verbose) cerr << info_str
#define cerr_verbose_cont if (FLAGS_verbose) cerr
#define cerr_detail if (FLAGS_detail) cerr << detl_str
#define cerr_detail_cont if (FLAGS_detail) cerr
#define cerr_warning cerr << warn_str
#define cerr_warning_cont cerr

#define SHORT_FILENAME (strrchr(__FILE__, '/') ? strrchr(__FILE__, '/') + 1 : __FILE__)
#define SYSERROR(info) std::system_error(errno, std::generic_category(), \
    std::string(info) + ": " + std::string(SHORT_FILENAME) + ":" + std::to_string(__LINE__))
#define throw_syserror(info) throw SYSERROR(info)
#define warn_syserror(info) cerr_warning << SYSERROR(info).what() << endl

#define addr_to_string_delim(addr, delim) (string(inet_ntoa((addr).sin_addr)) + (((addr).sin_port != 0) ? ((delim) + \
    to_string(((delim) == ':') ? ntohs((addr).sin_port) : (addr).sin_port)) : ""))
#define addr_to_string(addr) addr_to_string_delim(addr, ':')

void init_prompt_color();

// a < b
struct cmp_addr_less {
    bool operator()(const struct sockaddr_in& a, const struct sockaddr_in& b) const;
};

struct cmp_addr_no_port_less {
    bool operator()(const struct sockaddr_in& a, const struct sockaddr_in& b) const;
};

// a == b
struct cmp_addr_equal {
    bool operator()(const struct sockaddr_in& a, const struct sockaddr_in& b) const;
};

struct sockaddr_in convert_addr(const char *addr, char delim = ':');

vector<string> tokenize(const string &s);
string stringify(const vector<string> &t, size_t start=0, const string &delim=" ");

#endif //REDISTMET_COMMON_H

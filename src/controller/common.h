//
// Created by tangruize on 22-5-10.
//

#ifndef TPROXY_COMMON_H
#define TPROXY_COMMON_H

#include <arpa/inet.h>
#include <sys/socket.h>
#include <gflags/gflags.h>

#include <iostream>
#include <string>
#include <map>
#include <vector>
#include <fstream>
#include <sstream>
#include <cstring>

#include "ConfigFile.h"
#include "Command.h"

using namespace std;

DECLARE_bool(verbose);
DECLARE_bool(detail);

extern string info_str;
extern string warn_str;
extern string detail_str;

#define cerr_verbose if (FLAGS_verbose) cerr << info_str
#define cerr_verbose_cont if (FLAGS_verbose) cerr
#define cerr_detail if (FLAGS_detail) cerr << detail_str
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
#define cidr_to_string(addr) addr_to_string_delim(addr, '/')

extern ConfigFile configFile;
extern Command command;

#endif //TPROXY_COMMON_H

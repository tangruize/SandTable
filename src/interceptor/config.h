//
// Created by tangruize on 22-5-14.
//

#ifndef MYSYSCALL_CONFIG_H
#define MYSYSCALL_CONFIG_H

#ifndef CONFIG_FILE_ENV
#define CONFIG_FILE_ENV "MYSYSCALL_CONFIG"
#endif
#ifndef NODE_NO_ENV
#define NODE_NO_ENV "SSH_NO"
#endif

#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdio.h>
#include <unistd.h>

// #ifdef __linux__
// #define ROUTER_FD 1022
// #elif defined(__unix__)
// #define ROUTER_FD 126 // openbsd max is 128?
// #endif
#define ROUTER_FD 126

//#define ADDR_FMT "%s:%d"
//#define ADDR_TO_STR(addr) rstr1(inet_ntoa(((const struct sockaddr_in*)addr)->sin_addr)), ntohs(((const struct sockaddr_in*)addr)->sin_port)
//#define ADDR_TO_STR2(addr) rstr2(inet_ntoa(((const struct sockaddr_in*)addr)->sin_addr)), ntohs(((const struct sockaddr_in*)addr)->sin_port)
//#define CIDR_FMT "%s/%d"
//#define CIDR_TO_STR(addr) rstr1(inet_ntoa(((const struct sockaddr_in*)addr)->sin_addr)), ((const struct sockaddr_in*)addr)->sin_port
//#define CIDR_TO_STR2(addr) rstr2(inet_ntoa(((const struct sockaddr_in*)addr)->sin_addr)), ((const struct sockaddr_in*)addr)->sin_port

#define ADDR_FMT "%s"
#define CIDR_FMT "%s"
#define ADDR_TO_STR(addr) addr_to_str((const struct sockaddr_in *)addr, ":", 1)
#define ADDR_TO_STR2(addr) addr_to_str((const struct sockaddr_in *)addr, ":", 2)
#define CIDR_TO_STR(addr) addr_to_str((const struct sockaddr_in *)addr, "/", 1)
#define CIDR_TO_STR2(addr) addr_to_str((const struct sockaddr_in *)addr, "/", 2)

#ifdef __cplusplus
extern "C" {
#endif

// read config file (get filename from ENV CONFIG_FILE_ENV), store concerned addr
void init_config_file();

struct sockaddr_in convert_mapped_ipv6_to_ipv4(const struct sockaddr_in6 *addr);

// check addr is concerned, so that we can trace later actions of the fd
int check_addr_is_concerned(const struct sockaddr_in *addr);
int check_addr_is_concerned_with_len(const struct sockaddr_in *addr, socklen_t addrlen);

// add fd to concerned fd list
void add_concerned_fd(int fd, const struct sockaddr_in *addr, int is_accept);

// remove fd (close())
void rm_concerned_fd(int fd);

// check fd is concerned to do some actions (send()/sendto())
int check_fd_is_concerned(int fd);
struct sockaddr_in check_fd_is_concerned_with_addr(int fd);
int get_addr_fd(struct sockaddr_in addr);

// convert addr to printable string (both ipv4 and ipv6)
const char *addr_to_str(const struct sockaddr_in *addr, const char *delim, int which);

// convert ADDR (format: xxx.xxx.xxx.xxx:port) and CIDR (format: xxx.xxx.xxx.xxx/netmask)
struct sockaddr_in convert_addr(const char *addr, char delim);

// get tokens from line. (CPP only, ts is (vector<string> *) type)
int get_tokens(const char *line, void *ts);

// get addr from node name (str).
struct sockaddr_in get_node_addr(const char *node);

extern int log_stdout_fd;
extern int log_stderr_fd;

// get log fd
static inline int get_log_fd(int fd) {
    if (fd == STDOUT_FILENO)
        return log_stdout_fd;
    else if (fd == STDERR_FILENO)
        return log_stderr_fd;
    else
        return -1;
}

struct collector_popen {
    pid_t child_pid;
    int from_child, to_child;
};

// for state collector
extern struct collector_popen collector_childinfo;

// node number
extern const char* node_id;

// bool: multi ports support
extern int option_multi_ports;
// bool: not to clear states when state collect
extern int option_state_no_clear;
// bool: not to fail when a variable is empty
extern int option_state_no_fail_empty;

#ifdef __cplusplus
}
#endif

#endif //MYSYSCALL_CONFIG_H

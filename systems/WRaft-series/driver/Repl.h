//
// Created by tangruize on 2/14/23.
//

#ifndef REDISTMET_REPL_H
#define REDISTMET_REPL_H

#include <string>

using namespace std;

class Repl {
private:
    const char *prompt   = "\033[1;36m" "(REPL) " "\033[0m";
    const char *ok_str   = "\033[1;32m" "[OK]"    "\033[0m";  // bold green
    const char *fail_str = "\033[1;31m" "[FAIL]"  "\033[0m";  // bold red
    // int interceptor_fd = 1022;
    int interceptor_fd = 126;
    void check_interceptor_fd();
    void ack(const string &data) const;
public:
    Repl();
    void readline();
    bool getinfo(const string &cmd);
};


#endif //REDISTMET_REPL_H

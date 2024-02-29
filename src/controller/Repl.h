//
// Created by fedora on 5/25/22.
//

#ifndef TPROXY_REPL_H
#define TPROXY_REPL_H

class Repl {
private:
    const char *prompt = "\033[1;36m" "(REPL) " "\033[0m";
public:
    Repl();
    void readline();
};


#endif //TPROXY_REPL_H

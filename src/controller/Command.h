//
// Created by tangruize on 22-5-18.
//

#ifndef TPROXY_COMMAND_H
#define TPROXY_COMMAND_H

#include <string>
#include <vector>
#include <thread>
#include <cassert>

//#include <readerwriterqueue.h>
#include <concurrentqueue/blockingconcurrentqueue.h>

using namespace std;
using namespace moodycamel;

struct cmd_t {
    vector<string> tokens;
    cmd_t() = default;
    cmd_t(const string &line);
    cmd_t &operator=(cmd_t &&c) noexcept {
        tokens = std::move(c.tokens);
        return *this;
    }
    cmd_t(cmd_t &&c) noexcept {
        *this = std::move(c);
    }
    const string &get_cmd() const {
        assert(!tokens.empty());
        return tokens.front();
    }
    const string &get_arg(int n) const {
        return tokens[n];
    }
    string get_args_from(unsigned start) const;
    bool check_prompt_invalid(unsigned argc=0, const string &info="", bool at_least=false) const;
    bool prompt_invalid(const string &info) const { return check_prompt_invalid(0, info); }
    bool empty() { return tokens.empty(); }
    friend std::ostream & operator<<(std::ostream &os, const cmd_t& c);
    void shift() {
        if (!tokens.empty())
            tokens.erase(tokens.begin());
    }
    size_t size() {
        return tokens.size();
    }
};

class Command {
private:
//    BlockingReaderWriterQueue<cmd_t> cmds;
    BlockingConcurrentQueue<cmd_t> cmds;
    bool is_file;
    int max_loop_times;
    bool no_abrt = false;
public:
    Command(int max_loop_times_ = 10);
    void read_file(const string &file);
    bool enqueue(const string &line);
    bool enqueue(cmd_t &&c);
    bool dequeue(cmd_t &c);
    void run_read_cmd();
    void set_file_mode();
    void set_cmd_mode();
    void set_loop_times(int value);
    void set_no_abrt();
    string shell(const string &cmd, bool blocking=true);
    std::thread run_read_cmd_background() { return std::thread( [this] { this->run_read_cmd(); } ); }
};

#endif //TPROXY_COMMAND_H

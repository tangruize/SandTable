//
// Created by tangruize on 22-5-18.
//

#include "common.h"
#include "Command.h"
#include "TcpNetwork.h"
#include "UdpNetwork.h"
#include <thread>

DECLARE_bool(delay_connect);
DECLARE_int32(block_connect_timeout);
DECLARE_bool(half_duplex_connection);
DECLARE_bool(state_no_fail_empty);
DECLARE_bool(udp);

void Command::read_file(const string &file) {
    cerr_verbose << "Read command file \"" << file << "\"" << endl;
    ifstream f(file);
    if (!f.is_open()) {
        throw_syserror("ifstream open");
//        cerr_warning << "read_file cannot open file: " << file << endl;
        return;
    }
    string line;
    int line_count = 0;
    while (getline(f, line)) {
        if (enqueue(line))
            line_count++;
    }
    if (is_file)
        enqueue("exit");
    cerr_detail << "Read " << line_count << " commands in file \"" << file << "\"" << endl;
}

bool Command::enqueue(const string &line) {
    cmd_t cmd(line);
    if (cmd.empty())
        return false;
    cmds.enqueue(std::move(cmd));
    return true;
}

bool Command::dequeue(cmd_t &c) {
    if (is_file) {
        if (!cmds.try_dequeue(c))
            return false;
    } else {
        cmds.wait_dequeue(c);
    }
    if (c.get_cmd() == "exit")
        return false;
    return true;
}

Command::Command(int max_loop_times_) {
    is_file = configFile.get_strategy() == STRATEGY_FILE;
    max_loop_times = max_loop_times_;
}

bool Command::enqueue(cmd_t &&c) {
    if (c.empty())
        return false;
    cmds.enqueue(std::move(c));
    return true;
}

bool cmd_t::check_prompt_invalid(unsigned argc, const string &info, bool at_least) const {
    assert(!tokens.empty());
    bool ok = at_least ? (argc <= tokens.size()) : (argc == tokens.size());
    if (ok) {
        return true;
    }
    string required_prompt = argc ? string(" (requires ") + (at_least ? ">=" : "") + to_string(argc) + " fields)" : "";
    cerr_warning << "Invalid cmd" << required_prompt;
    if (!info.empty()) {
        cerr_warning_cont << ": " << info;
    }
    cerr_warning_cont << ": \"";
    cerr_warning_cont << get_cmd();
    for (unsigned i = 1; i < tokens.size(); i++) {
        cerr_warning_cont << " " << tokens[i];
    }
    cerr_warning_cont << "\"" << endl;
    return false;
}

std::ostream &operator<<(ostream &os, const cmd_t &c) {
    os << c.get_cmd();
    for (unsigned i = 1; i < c.tokens.size(); i++) {
        cerr_warning_cont << " " << c.tokens[i];
    }
    return os;
}

cmd_t::cmd_t(const string &line) {
    istringstream ss(line);
    string token;
    while (getline(ss, token, ' ')) {
        if (token.empty())
            continue;
//        if (token[0] == '#')
//            break;
        tokens.push_back(token);
    }
}

string cmd_t::get_args_from(unsigned start) const {
    assert(start < tokens.size());
    string res = tokens[start];
    for (unsigned i = start + 1; i < tokens.size(); ++i) {
        res += " " + tokens[i];
    }
    return res;
}

void Command::run_read_cmd() {
    cmd_t c;
    int cmd_counter = 0;
#define CHECK_ARGS_MORE(argc, m) if (!c.check_prompt_invalid(argc, "", m)) continue; else cerr_verbose << "Read cmd (line " << cmd_counter <<  "): " << c << endl
#define CHECK_ARGS(argc) CHECK_ARGS_MORE(argc, false)
    bool is_loop = false, finish_loop = false;
    int loop_times = 0;
    string compare_cache_name, model_var, last_exec_node, model_variable_node, shell_result;
    while (true) {
        if (!is_loop || finish_loop) {
            if (!command.dequeue(c))
                break;
            cmd_counter ++;
            is_loop = false;
            finish_loop = false;
        } else {
            loop_times ++;
            if (loop_times % 2 == 0) {
                std::this_thread::sleep_for(std::chrono::milliseconds(100));
            }
            if (loop_times == max_loop_times) {
                cerr_warning << "Loop more than " << max_loop_times << " times! Canceled" << endl;
                loop_times = 0;
                is_loop = false;
                continue;
            }
        }
        if (c.get_cmd() == "loop") {
            CHECK_ARGS_MORE(1, true);
            is_loop = true;
            c.shift();
        }
        if (c.get_cmd() == "deliver") {
            if (!FLAGS_udp) {
                CHECK_ARGS(3);
                if (!net->deliver(c.get_arg(1), c.get_arg(2), false)) {
                    c.prompt_invalid("deliver failed");
                }
            } else {
                CHECK_ARGS(2);
                if (!udpNet->deliver(stoi(c.get_arg(1)))) {
                    c.prompt_invalid("cannot find message");
                }
            }
        } else if (c.get_cmd() == "deliver-unordered") {  // tcp only
            CHECK_ARGS(4);
            if (!net->deliver_unordered(c.get_arg(1), c.get_arg(2), std::atoi(c.get_arg(3).c_str()))) {
                c.prompt_invalid("deliver-unordered failed");
            }
        } else if(c.get_cmd() == "send") {
            CHECK_ARGS(4);
            char* data;
            const int len = c.get_arg(3).length();
            data = new char[len + 1];
            stpcpy(data, c.get_arg(3).c_str());
            if (!udpNet->sendData(c.get_arg(1), c.get_arg(2), data)) {
                c.prompt_invalid("sendData wrong");
            }
        } else if(c.get_cmd() == "drop") {
            CHECK_ARGS(2);
            if (!udpNet->dropMessage(stoi(c.get_arg(1)))) {
                c.prompt_invalid("cannot find message");
            }
        } else if(c.get_cmd() == "duplicate") {
            CHECK_ARGS(2);
            if (!udpNet->duplicateMessage(stoi(c.get_arg(1)))) {
                c.prompt_invalid("cannot find message");
            }
        } else if(c.get_cmd() == "block") {
            CHECK_ARGS(1);
            udpNet->set_block();
        } else if(c.get_cmd() == "unblock") {
            CHECK_ARGS(1);
            udpNet->set_unblock();
        } else if (c.get_cmd() == "status") {
            CHECK_ARGS(1);
            if (!FLAGS_udp) {
                net->print_status();
            } else {
                udpNet->print_status();
            }
        } else if (c.get_cmd() == "partition") {  // tcp only
            CHECK_ARGS(2);
            net->partition(c.get_arg(1));
        } else if (c.get_cmd() == "recover") {  // tcp only
            CHECK_ARGS(2);
            net->recover(c.get_arg(1));
        } else if (c.get_cmd() == "recover-reopen") {  // tcp only
            CHECK_ARGS(2);
            net->recover_no_disconnect(c.get_arg(1));
        } else if (c.get_cmd() == "wait-recover") {  // tcp only
            CHECK_ARGS(1);
            net->wait_recover();
        } else if (c.get_cmd() == "intercept") {
            CHECK_ARGS_MORE(3, true);
            if (!FLAGS_udp) {
                finish_loop = net->send_cmd(c.get_arg(1), c.get_args_from(2), cmd_counter);
            } else {
                finish_loop = udpNet->send_cmd(c.get_arg(1), c.get_args_from(2), cmd_counter);
            }
        } else if (c.get_cmd() == "init") {
            if (!FLAGS_udp) {
                CHECK_ARGS_MORE(2, true);
                if (c.size() == 2) {
                    net->init(std::stoi(c.get_arg(1)), 5000);
                } else {
                    net->init(std::stoi(c.get_arg(1)), stoi(c.get_arg(2)));
                }
            } else {
                CHECK_ARGS(2);
                udpNet->init(std::stoi(c.get_arg(1)));
            }
        } else if (c.get_cmd() == "wait-init") {  // tcp only
            CHECK_ARGS_MORE(2, true);
            if (c.size() == 2) {
                net->wait_init(std::stoi(c.get_arg(1)), FLAGS_half_duplex_connection, 5000);
            } else if (c.size() == 4) {
                net->wait_init(std::stoi(c.get_arg(1)), stoi(c.get_arg(2)), stoi(c.get_arg(3)));
            } else {
                cerr_warning << "Bad cmd argument number: " << c.size() << endl;
            }
        } else if (c.get_cmd() == "execute") {
            CHECK_ARGS_MORE(3, true);
            last_exec_node = c.get_arg(1);
            finish_loop = remote_control->send_cmd_ssh(c.get_arg(1), c.get_args_from(2));
        } else if (c.get_cmd() == "execute_asy") {
            CHECK_ARGS_MORE(3, true);
            last_exec_node = c.get_arg(1);
            finish_loop = remote_control->send_cmd_ssh_asy(c.get_arg(1), c.get_args_from(2));
        } else if (c.get_cmd() == "deliver-all") {
//            CHECK_ARGS(2);
            if (!FLAGS_udp) {
                CHECK_ARGS_MORE(2, true);
                if (c.size() == 2) {
                    net->deliver_all(std::stoi(c.get_arg(1)));
                } else {
                    if (!net->deliver(c.get_arg(1), c.get_arg(2), true))
                        c.prompt_invalid("deliver failed");
                }
            } else {
                CHECK_ARGS(2);
                udpNet->deliver_all(std::stoi(c.get_arg(1)));
            }
        } else if (c.get_cmd() == "compare") {
            CHECK_ARGS(2);
            if (c.get_arg(1) == "net") {
                string net_status;
                if (!FLAGS_udp) {
                    net_status = net->get_status_cache();
                } else {
                    net_status = udpNet->get_status_cache();
                }
                if (net_status != model_var) {
                    cerr_warning << "Net status is inconsistency!" << endl;
                    cerr_warning_cont << "- Code:" << endl;
                    cerr_warning_cont << net_status;
                    cerr_warning_cont << "- Model:" << endl;
                    cerr_warning_cont << model_var << flush;
                    // we don't abort controller, since the msg may arrive soon! and partitioned packets are not flushed!
//                    assert(net_status == model_var);
                }
            } else if (c.get_arg(1) == "variable") {  // "variable"
                string code_var = remote_control->get_cache_cmp_data();
                if (FLAGS_state_no_fail_empty && code_var == "(empty)") {
                    cerr_warning << "Code variable \"" << compare_cache_name << "\" is empty" << endl;
                }
                else if (code_var != model_var) {
                    cerr_warning << "Variable \"" << compare_cache_name << "\" compare failed!" << endl;
                    cerr_warning_cont << "- Code (" << last_exec_node << "): " << code_var << endl;
                    cerr_warning_cont << "- Model(" << model_variable_node << "): " << model_var << endl;
                    if (!no_abrt) {
                        assert(code_var == model_var);
                    }
                }
            } else if (c.get_arg(1) == "shell_result") {
                if (shell_result != model_var) {
                    cerr_warning << "Shell result \"" << compare_cache_name << "\" compare failed!" << endl;
                    cerr_warning_cont << "- Code: " << shell_result << endl;
                    cerr_warning_cont << "- Model(" << model_variable_node << "): " << model_var << endl;
                    if (!no_abrt) {
                        assert(shell_result == model_var);
                    }
                }
            } else if (c.get_arg(1) == "net-len") {
                string net_len = to_string(net->get_net_len());
                if (net_len != model_var) {
                    cerr_warning << "Net mgs length compare failed!" << endl;
                    cerr_warning_cont << "- Code: " << net_len << endl;
                    cerr_warning_cont << "- Model:" << model_var << endl;
                }
            }
            else { // "none"
                cerr_detail << "Not compared, just for reference" << endl;
            }
            compare_cache_name.clear();
            model_var.clear();
            remote_control->clear_cache_cmp_data();
        } else if (c.get_cmd() == "sleep" || c.get_cmd() == "nop") {  // sleep for a while to execute the next cmd
            CHECK_ARGS_MORE(1, true);
            int milliseconds = 1000;
            if (c.size() >= 2) {
                milliseconds = stoi(c.get_arg(1));
            }
            std::this_thread::sleep_for(std::chrono::milliseconds(milliseconds));
        } else if (c.get_cmd() == "connect-all") {  // connect pending connections  // tcp only
            CHECK_ARGS(1);
            net->connect_pending();
        } else if (c.get_cmd() == "disable") {
            CHECK_ARGS(2);
            if (c.get_arg(1) == "block_connect") {
                FLAGS_block_connect_timeout = -abs(FLAGS_block_connect_timeout);
            }
            if (c.get_arg(1) == "delay_connect") {
                FLAGS_delay_connect = false;
            }
        } else if (c.get_cmd() == "enable") {
            CHECK_ARGS_MORE(2, true);
            if (c.get_arg(1) == "block_connect") {
                if (c.size() == 2) {
                    if (FLAGS_block_connect_timeout < -1) {
                        FLAGS_block_connect_timeout = abs(FLAGS_block_connect_timeout);
                        cerr_detail << "block_connect = " << FLAGS_block_connect_timeout << endl;
                    } else {
                        cerr_warning << "Cannot enable block_connect due to unknown value to set" << endl;
                    }
                } else {
                    FLAGS_block_connect_timeout = stoi(c.get_arg(3));
                    cerr_detail << "block_connect = " << FLAGS_block_connect_timeout << endl;
                }
            } else {
                cerr_warning << "Not supported " << c.get_arg(1) << endl;
            }
        } else if (c.get_cmd() == "inspect_conn_fd") {
            CHECK_ARGS(2);
            net->print_connection_buffer(stoi(c.get_arg(1)));
        } else if (c.get_cmd() == "close_client") {
            CHECK_ARGS(2);
            net->close_client(c.get_arg(1));
        } else if (c.get_cmd() == "pre_close_client") {
            CHECK_ARGS(2);
            net->pre_close_client(c.get_arg(1));
        } else if (c.get_cmd() == "clear") {
            CHECK_ARGS(3);
            net->clear_channel_msgs(c.get_arg(1), c.get_arg(2));
        } else if (c.get_cmd() == "shell") {
            CHECK_ARGS_MORE(2, true);
            if (c.get_arg(1) == "-nonblocking") {  // e.g. put
//                CHECK_ARGS_MORE(3, true);  // it causes duplicate cmd print
                shell(c.get_args_from(2), false);
            } else {  // e.g. get
                shell_result = shell(c.get_args_from(1), true);
            }
        }
        else {
            if (c.get_cmd() == "#") {
                if (c.get_arg(1) == "msgs") {
                    model_var += c.get_args_from(1) + "\n";
                } else if (c.get_arg(1) == "variable") {
                    compare_cache_name = c.get_arg(2);
                    model_variable_node = c.get_arg(3);
                    model_var = c.get_args_from(4);
                } else if (c.get_arg(1) == "net-len") {
                    model_var = c.get_arg(2);
                }
                cerr_verbose << "Comment (line " << cmd_counter << "): " << c << endl;
                if (c.get_arg(1).starts_with('[')) {
                    // print cmd in each node
                    if (!FLAGS_udp) {
                        net->send_cmd_all("print", c.get_args_from(1), cmd_counter);
                    } else {
                        udpNet->send_cmd_all("print", c.get_args_from(1), cmd_counter);
                    }
                }
            } else {
                cerr_warning << "Unknown cmd: " << c << endl;
            }
        }
    }
//    for (auto it: fd_to_channel_status)
//        close(it.first);
}

void Command::set_file_mode() {
    is_file = true;
}

void Command::set_cmd_mode() {
    is_file = false;
}

void Command::set_loop_times(int value) {
    max_loop_times = value;
}

void Command::set_no_abrt() {
    no_abrt = true;
}

static string execute_shell(const string &cmd) {
    string result;
    FILE *fp;
    char buffer[1024];

    fp = popen(cmd.c_str(), "r");
    if (fp == nullptr) {
        cerr_warning << "execute_shell: failed to run: " << cmd << endl;
        return "";
    }

    while (fgets(buffer, sizeof(buffer), fp) != nullptr) {
        result += buffer;
    }
    pclose(fp);

    result.erase(result.find_last_not_of('\n') + 1);  // rtrim
    cerr_detail << "Shell cmd finished: \"" << cmd << "\", result: " << (result.empty() ? "(EOF)" : result) << endl;
    return result;
}

string Command::shell(const string &cmd, bool blocking) {
    if (!blocking) {
        std::thread background_thread(execute_shell, cmd);
        background_thread.detach();
        return "";  // no result to obtain
    } else {
        return execute_shell(cmd);
    }
}

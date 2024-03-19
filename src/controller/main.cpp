//
// Created by tangruize on 22-5-10.
//

#include "TcpSocket.h"
#include "UdpSocket.h"
#include "ConfigFile.h"
#include "TcpNetwork.h"
#include "UdpNetwork.h"
#include "Repl.h"
#include "RemoteControl.h"

#include <unistd.h>
#include <csignal>

#include <gflags/gflags.h>
using namespace gflags;

DECLARE_bool(help);
DEFINE_bool(verbose, false, "Show verbose information");
DEFINE_bool(detail, false, "Show detail information");
DEFINE_string(config, "", "Config file");
DEFINE_int32(port, -1, "Port to bind");
DEFINE_string(tmpdir, "", "Environment TMPDIR for ssh control");
DEFINE_int32(sshno, -1, "Environment SSH_NO to exclude controller itself ssh control");
DEFINE_bool(deliver_first_msg, false, "Directly deliver first msg after connected");
DEFINE_bool(no_exit, false, "No exit if all cmds are executed");
DEFINE_int32(max_loop_times, 40, "Wait cmd loop times, every 2 loops wait 10ms");
DEFINE_bool(no_abrt, false, "No abort if conformance check failed");
DEFINE_bool(half_duplex_connection, false, "Connections are half-duplex");
DEFINE_bool(delay_connect, false, "Connecting to peer is delayed");
DEFINE_int32(block_connect_timeout, -1, "Blocking until connected to peer");
DEFINE_int32(merge_small_msg, -1, "Merge small msgs which are less than this value");
DEFINE_bool(dump_msg, false, "Dump msg content for debug");
DEFINE_bool(no_exec_ack, false, "Not to get ack after sending execute cmd");
DEFINE_double(add_ssh_timeout, -1, "Add ssh node when init, and set the add timeout");
DEFINE_bool(multi_ports, false, "Enable multiple ports");
DEFINE_string(deliver_first_msg_ports, "", "A port lists separated by comma to deliver first msg");
DEFINE_bool(abort_failed_init, false, "Abort when init failed");
DEFINE_bool(state_no_fail_empty, false, "Not to abort when code state is empty");
DEFINE_bool(partition_keep_msgs, false, "Keep messages and allow delivery when partitioned");
// Backward compatibility for WRaft exp, which originally uses UDP
DEFINE_bool(allow_msg_unordered, false, "Downgrade TCP to allow unordered delivery");
DEFINE_bool(udp, false, "Network type is UDP");

ConfigFile configFile;
Command command;

string info_str = "[INFO] ";
string warn_str = "[WARN] ";
string detail_str = "[DETL] ";

int main(int argc, char **argv) {
    // Parse arguments and show help
    SetUsageMessage("Intercept network TCP/UDP connections using TPROXY");
    ParseCommandLineNonHelpFlags(&argc, &argv, true);
    if (FLAGS_help || argc != 1) {
        ShowUsageWithFlagsRestrict(argv[0], "main");
        exit(1);
    }
    else if (FLAGS_detail) {
        FLAGS_verbose = true;
    }
    if (FLAGS_multi_ports) {  // multi ports need to know if the connection is created by connect or accept
        FLAGS_half_duplex_connection = true;
    }
    if (isatty(STDERR_FILENO)) {
        info_str = "\033[1;32m" + info_str + "\033[0m";  // bold green
        warn_str = "\033[1;31m" + warn_str + "\033[0m";  // bold red
        detail_str = "\033[1;34m" + detail_str + "\033[0m";  // bold blue
    }

    if (FLAGS_port != -1)
        configFile.set_port(FLAGS_port);
    if (!FLAGS_deliver_first_msg_ports.empty())
        configFile.init_port_to_deliver_first_msg(FLAGS_deliver_first_msg_ports);
    configFile.load(FLAGS_config);
    signal(SIGPIPE, SIG_IGN);

    if (configFile.get_strategy() == STRATEGY_NOT_SET) {
        ShowUsageWithFlagsRestrict(argv[0], "main");
        exit(1);
    }
    RemoteControl remoteControl;
    remote_control = &remoteControl;
    if (FLAGS_add_ssh_timeout > 0)
        remote_control->try_add_node(FLAGS_add_ssh_timeout);
    vector<thread> threads;
    command.set_loop_times(FLAGS_max_loop_times);
    if (FLAGS_no_abrt)
        command.set_no_abrt();
    if (!FLAGS_udp) {
        TcpSocket tcpSocket(configFile.get_port());
        TcpNetwork tcpNetwork(&tcpSocket, FLAGS_half_duplex_connection);
        net = &tcpNetwork;
        switch (configFile.get_strategy()) {
            case STRATEGY_DIRECT:
                tcpNetwork.run_epoll();
                break;
            case STRATEGY_FILE:
                tcpNetwork.run_epoll_background().detach();
                command.set_file_mode();
                command.read_file(configFile.get_cmd_file());
                command.run_read_cmd();
                if (FLAGS_no_exit) {
                    command.set_cmd_mode();
                    threads.push_back(command.run_read_cmd_background());
                    Repl repl;
                    repl.readline();
                }
                break;
            case STRATEGY_CMD: {
                tcpNetwork.run_epoll_background().detach();
                threads.push_back(command.run_read_cmd_background());
                Repl repl;
                repl.readline();
                break;
            }
            default:
                assert(0);
        }
    } else {
        UdpSokcet udpSocket(configFile.get_port());
        signal(SIGPIPE, SIG_IGN);
        UdpNetwork udpNetwork(&udpSocket);
        udpNet = &udpNetwork;
        switch (configFile.get_strategy()) {
        case STRATEGY_DIRECT:
            udpNetwork.run_epoll();
            break;
        case STRATEGY_FILE:{
            udpNetwork.run_epoll_background().detach();
            command.set_file_mode();
            command.read_file(configFile.get_cmd_file());
            command.run_read_cmd();
            if (FLAGS_no_exit) {
                command.set_cmd_mode();
                threads.push_back(command.run_read_cmd_background());
                Repl repl;
                repl.readline();
            }
            break;
        }
        case STRATEGY_CMD: {
            udpNetwork.run_epoll_background().detach();
            threads.push_back(command.run_read_cmd_background());
            Repl repl;
            repl.readline();
            break;
        }
        default:
            assert(0);
        }
    }
    for (auto &i: threads) {
        i.join();
    }
}

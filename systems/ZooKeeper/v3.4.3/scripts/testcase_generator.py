import sys
import os
import jq
import json
import argparse
import shutil
import signal

show_status=True

def set_path():
    def dirname_level_up(name, level):
        for _ in range(level):
            name = os.path.dirname(name)
        return name

    script_dir = os.path.dirname(os.path.realpath(__file__))
    deps_dir = os.path.join(dirname_level_up(script_dir, 4), 'scripts')
    sys.path.append(deps_dir)

set_path()

from trace_reader import TraceReader

# def sigint_handler(signum, frame):
#     print('TC-Gen Caught SIGINT, Ctrl+C again to exit')
#     signal.signal(signal.SIGINT, signal.SIG_DFL)
#
#
# signal.signal(signal.SIGINT, sigint_handler)

default_config = 'config.txt'
default_output = 'traces.txt'
default_conn_fd = 126
default_node_port = 2333
default_debug = False
nodes = dict()
node_port = None


def parse_args():
    parser = argparse.ArgumentParser(description="Test case generator for Xraft")
    parser.add_argument(dest='trace_file', action='store', help='Trace file')
    parser.add_argument('-c', dest='config', action='store', required=True, help='Config file',
                        default=default_config)
    parser.add_argument('-o', dest='output', action='store', required=False, help='Output trace file',
                        default=default_output)
    parser.add_argument('-f', dest='conn_fd', action='store', required=False,
                        help='Interceptor<->Controller connection fd', default=default_conn_fd)
    parser.add_argument('-n', dest='node_port', action='store', required=False, help='Port of test nodes',
                        default=default_node_port)
    parser.add_argument('-d', dest='debug', action='store_true', required=False, help='Print debug msg',
                        default=default_debug)
    parser.add_argument('-i', dest='in_place', action='store_true', required=False, help='Generate in current dir',
                        default=False)
    parser.add_argument('-I', dest='in_dir', action='store', required=False,
                        help='Generate in the specific dir under trace dir', default='')
    arg_parser = parser.parse_args()
    if not arg_parser.in_place:
        arg_parser.trace_file = os.path.realpath(arg_parser.trace_file)
        arg_parser.config = os.path.realpath(arg_parser.config)

        if arg_parser.in_dir:
            dir_name = os.path.join(os.path.dirname(arg_parser.trace_file), arg_parser.in_dir)
            os.makedirs(dir_name, mode=0o755, exist_ok=True)
        else:
            dir_name = os.path.dirname(arg_parser.trace_file)
        base_name = os.path.basename(arg_parser.trace_file)
        test_case_dir = base_name + '.dir'
        # new_name = os.path.join(test_case_dir, base_name)

        os.chdir(dir_name)
        os.makedirs(test_case_dir, mode=0o755, exist_ok=True)
        # os.mkdir(test_case_dir, mode=0o755)
        # os.rename(arg_parser.trace_file, new_name)
        # arg_parser.trace_file = new_name
        os.chdir(test_case_dir)

    return arg_parser


def eprint(*largs, **kvargs):
    if args.debug:
        print(*largs, **kvargs, file=sys.stderr)


def read_config():
    global nodes, node_port
    with open(args.config) as f:
        map_cidr = dict()
        for line in f:
            line = line.strip()
            if line.startswith('map-cidr'):
                _, fake, real = [cidr.replace('.0/24', '') for cidr in line.split(' ', 3)]
                map_cidr[real] = fake
                eprint('Read cmd:', 'map-cidr', fake + '.0/24', real + '.0/24')
            elif line.startswith('node'):
                _, name, ip = line.split(' ', 3)
                for k, v in map_cidr.items():
                    if k in ip:
                        nodes[name] = ip.replace(k, v)
                        eprint('Read cmd:', 'node', name, nodes[name])
                        break
            elif line.startswith('router'):
                _, router_addr = line.split(' ', 2)
                _, router_port = router_addr.split(':', 2)
                try:
                    router_port = int(router_port)
                    node_port = router_port
                except Exception:
                    eprint('Router port is invalid')
                    pass
            else:
                eprint('Ignored cmd:', line)
    if node_port is None:
        node_port = args.node_port


def check_test_code_is_generated(config_file, testcase_in_parent_dir):
    if args.in_place:
        return False
    for i in nodes.keys():
        if os.path.exists(os.path.join(os.path.dirname(config_file) if testcase_in_parent_dir else '.', i + '.py')):
            return True
    return False


def yield_trace(states):
    def compare(n, code_var_name, model_var_name, no_compare=False):
        pass
    def do_tick(n, is_compare=True):
        yield ['sleep', '500']  # sleep to wait the node processing
    fle_actions = {"ReceiveNotmsg", "NotmsgTimeout", "HandleNotmsg", }
    def deliver(src, dst, action, deliver_all=False):
        if action in fle_actions:
            port = "3888"
        else:
            port = "2888"
        yield ['deliver' if not deliver_all else "deliver-all", src, dst + ":" + port]
        # yield ['loop', 'intercept', dst, 'check_has_recv_queue', src]
        yield from do_tick(dst)
    jq_trace = jq.compile('.[].netcmd')
    jq_msgs = jq.compile('.[].msgs')
    jq_election_msgs = jq.compile('.[].electionMsgs')
    states_counter = 0
    leader_shutdown_state = None
    prev_state = None
    for i, msg, election_msgs, cur_state in zip(jq_trace.input(states), jq_msgs.input(states), jq_election_msgs.input(states), states):
        states_counter += 1
        if len(i) > 1:
            comment = i[0]
            netcmd = i[1]
            cmd, *parameters = netcmd
            yield ['#', '[' + str(states_counter) + ']'] + list(map(str, comment))
            yield ['#', str(json.dumps(netcmd))]
            if cmd == 'conn_del_flush':  # NodeCrash
                yield ['disable', 'block_connect']
                yield ['sleep', '3000']
                yield ['execute', comment[1], "#crash"]
                yield ['sleep', '1000']
                if comment[-1] == 'LeaderShutdown':
                    leader_shutdown_state = prev_state['state']
            elif cmd == 'conn_add':  # NodeStart
                yield ['enable', 'block_connect']
                yield ['execute', comment[1], "#restart"]
                yield ['sleep', '1000']
            elif cmd == 'msg_del':  # recv msg (deliver to node)
                # if comment[0] == 'FollowerProcessSyncMessage':
                #     yield from deliver(parameters[1], parameters[0], comment[0], True)  # deliver-all to sync
                #     yield ['sleep', '1000']
                #     yield from deliver(parameters[0], parameters[1], comment[0], True)
                # elif comment[0] == 'LeaderProcessACKEPOCH':
                #     yield from deliver(parameters[1], parameters[0], comment[0])
                #     yield ['sleep', '1000']
                #     yield from deliver(parameters[0], parameters[1], comment[0])
                #     yield from deliver(parameters[0], parameters[1], comment[0])
                #     yield ['sleep', '1000']
                #     yield from deliver(parameters[1], parameters[0], comment[0], True)
                # else:
                #     yield from deliver(parameters[1], parameters[0], comment[0])
                yield from deliver(parameters[1], parameters[0], comment[0])
            elif cmd == 'msg_add':  # send msg (enqueued in controller)
                # assert False
                if comment[0] == 'ConnectAndFollowerSendFOLLOWERINFO':
                    yield ['sleep', '1000']
            elif cmd == 'msg_add_dropped':  # send msg but dropped due to partition
                # assert False
                pass
            elif cmd == 'msg_reply':  # recv (deliver) msg and send (enqueue) msg
                yield from deliver(parameters[1], parameters[0], comment[0])
            elif cmd == 'msg_reply_dropped':  # reply but dropped
                yield from deliver(parameters[1], parameters[0], comment[0])
            elif cmd == 'msg_batch_add':  # batch send msgs
                if comment[0] == "ZabTimeout":
                    if leader_shutdown_state is not None:
                        if leader_shutdown_state[comment[1]] == 'LEADING':
                            for _ in range(2):
                                yield ['intercept', comment[1], 'inc_time_ms', '2100']
                        leader_shutdown_state = None
                    yield ['sleep', '2000']
                if comment[0] == 'NotmsgTimeout':
                    yield ['intercept', comment[1], 'inc_time_ms', '210']
                pass
            elif cmd == 'msg_batch_add_reply':  # recv msg and batch send msgs
                # yield ['deliver', parameters[1], parameters[0]]
                yield from deliver(parameters[1], parameters[0], comment[0])
        else:
            comment = i[0]
            # if comment[0] == 'Init':
            #     yield ['sleep', '5000']  # sleep 5 seconds to wait nodes init
            if comment[0] == 'WaitNewNotmsg' and comment[-1] == 'timeout':
                yield ['intercept', comment[1], 'inc_time_ms', '210']
                if comment[-2] == "LEADING":
                    yield ['sleep', '1000']
                else:
                    yield ['sleep', '500']
            # for j in nodes:
            #     yield from do_tick(j)
        if show_status:
            yield ['status']
            for src in nodes:
                msgs_info_str = 'msgs {}:'.format(src)
                for dst in nodes:
                    if src != dst:
                        msgs_info_str += ' {}({})'.format(dst, len(msg[src][dst]) + len(election_msgs[src][dst]))
                yield ['#', msgs_info_str]
            yield ['compare', 'net']
        prev_state = cur_state
    yield ['sleep', '500']
    eprint("Finish write:", args.output)

def copy_config_file(config_file, testcase_in_parent_dir):
    try:
        if testcase_in_parent_dir:
            os.symlink(os.path.dirname(config_file), 'config')
        else:
            shutil.copy2(config_file, os.path.join('..' if testcase_in_parent_dir else '.', os.path.basename(config_file)))
    except:
        pass

def gen_trace():
    tr = TraceReader(True)
    try:
        os.symlink(args.trace_file, 'tlc_trace.txt')
    except:
        pass
    states = list(tr.trace_reader(args.trace_file))
    eprint('Read states:', len(states))
    traces = list(yield_trace(states))
    with open('traces.txt', 'w') as f:
        # for i in traces:
        #     try:
        #         ' '.join(i)
        #     except:
        #         print(i)
        f.write('\n'.join(' '.join(i) for i in traces))

if __name__ == '__main__':
    args = parse_args()
    read_config()
    copy_config_file(args.config, not args.in_place)
    gen_trace()

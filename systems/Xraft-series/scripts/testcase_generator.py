import sys
import os
import jq
import json
import argparse
import shutil
import signal

show_status=True

cli_path=''
def set_path():
    global cli_path

    def dirname_level_up(name, level):
        for _ in range(level):
            name = os.path.dirname(name)
        return name

    script_dir = os.path.dirname(os.path.realpath(__file__))
    deps_dir = os.path.join(dirname_level_up(script_dir, 3), 'scripts')
    sys.path.append(deps_dir)
    # print(sys.path)
    cli_path = os.path.join(os.path.join(dirname_level_up(script_dir, 1), "kv-store"), "cli.sh")
    # print(cli_path)

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
# default_conn_fd = 1022
default_conn_fd = 126
default_node_port = 2333
default_client_port = 3333
default_debug = False
nodes = dict()
node_port = None


def parse_args():
    global cli_path
    parser = argparse.ArgumentParser(description="Test case generator for Xraft")
    parser.add_argument(dest='trace_file', action='store', help='Trace file')
    parser.add_argument('-c', dest='config', action='store', required=True, help='Config file',
                        default=default_config)
    parser.add_argument('-o', dest='output', action='store', required=False, help='Output trace file',
                        default=default_output)
    parser.add_argument('-p', dest='path', action='store', required=False, help='Xraft path',
                        default=None)
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
    if cli_path != arg_parser.path and arg_parser.path is not None:
        cli_path = os.path.join(arg_parser.path, "kv-store", "cli.sh")

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
        pass  # do not compare in xraft
    def do_tick(n, is_compare=True):
        yield ['sleep', '2000']  # sleep 2s to wait the node processing
    def deliver(src, dst):
        yield ['deliver', src, dst]
        # yield ['loop', 'intercept', dst, 'check_has_recv_queue', src]
        yield from do_tick(dst)
    def compare(dst):
        nonlocal prev_state, cur_state
        try:
            if prev_state is not None:
                if prev_state['state'][dst] != cur_state['state'][dst]:
                    yield ['intercept', dst, 'state_collect']
                    yield ['sleep', str(400)]
                    yield ['#', 'variable', 'state', dst, cur_state['state'][dst]]
                    yield ['intercept', dst, 'state_get', 'state']
                    yield ['compare', 'variable']
                    yield ['#', 'variable', 'current_term', dst, str(cur_state['current_term'][dst])]
                    yield ['intercept', dst, 'state_get', 'current_term']
                    yield ['compare', 'variable']
                if cur_state['netcmd'][0][0] in {'RecvAppendentriesResponse', 'RecvAppendentries'} and cur_state['netcmd'][0][1] in {'success', 'success retry'}:
                    yield ['intercept', dst, 'state_collect']
                    yield ['sleep', str(400)]
                    yield ['#', 'variable', 'commit_idx', dst, str(cur_state['commit_idx'][dst])]
                    yield ['intercept', dst, 'state_get', 'commit_idx']
                    yield ['compare', 'variable']
        except Exception as e:
            print(prev_state['state'], cur_state['state'], dst)
            raise e

    partitioned_nodes = []
    jq_trace = jq.compile('.[].netcmd')
    jq_msgs = jq.compile('.[].msgs')
    states_counter = 0
    prev_state = None
    for i, msg, cur_state in zip(jq_trace.input(states), jq_msgs.input(states), states):
        states_counter += 1
        comment = i[0]
        if len(i) > 1:
            netcmd = i[1]
            cmd, *parameters = netcmd
            yield ['#', '[' + str(states_counter) + ']'] + [str(c) for c in comment]
            yield ['#', json.dumps(netcmd)]
            if cmd == 'conn_part_flush':
                partitioned_nodes.append(parameters[0][0])
                yield ['partition', parameters[0][0]]
            elif cmd == 'conn_cure':  # network cure
                for n in partitioned_nodes:
                    yield ['recover', n]
                    # yield ['wait-recover']
                partitioned_nodes = []
            elif cmd == 'msg_del':  # recv msg (deliver to node)
                yield from deliver(parameters[1], parameters[0])
                yield from compare(parameters[0])
            elif cmd == 'msg_add':  # send msg (enqueued in controller)
                assert False
                pass  # not used
            elif cmd == 'msg_add_dropped':  # send msg but dropped due to partition
                assert False
                pass  # not used
            elif cmd == 'msg_reply':  # recv (deliver) msg and send (enqueue) msg
                yield from deliver(parameters[1], parameters[0])
                yield from compare(parameters[0])
            elif cmd == 'msg_reply_dropped':  # reply but dropped
                yield from deliver(parameters[1], parameters[0])
                yield from compare(parameters[0])
            elif cmd == 'msg_batch_add':  # batch send msgs
                if comment[0] == 'ElectionTimeout':
                    yield ['intercept', comment[1], 'inc_time_ms', '4100']  # > 4s
                elif comment[0] == 'SendAppendentriesAll':
                    yield ['intercept', comment[1], 'inc_time_ms', '1100']  # > 1s
                elif comment[0] == 'RecvEntry':
                    # pass
                    yield ['intercept', comment[1], 'inc_time_ms', '10'] # > ? (logReplicationReadTimeout)
                    yield ['shell', '-nonblocking', cli_path, comment[1], 'put', comment[2]]
                    yield ['sleep', '2000']  # wait it execute
                yield from do_tick(comment[1])
            elif cmd == 'msg_batch_add_reply':  # recv msg and batch send msgs
                # yield ['deliver', parameters[1], parameters[0]]
                yield from deliver(parameters[1], parameters[0])
                yield from compare(parameters[0])
        else:
            if comment[0] == 'Init':
                yield ['init', str(i[0][1])]
                yield ['sleep', '15000']  # sleep 15 seconds to wait nodes init
                # for j in nodes:
                #     yield from do_tick(j)
            elif comment[0] == 'ClientGetValue':
                yield ['#', 'variable', 'kvstore', comment[1], "null" if comment[2] == "Nil" else comment[2]]
                yield ['shell', cli_path, comment[1], 'get']
                yield ['compare', 'shell_result']
                yield from do_tick(comment[1])
        prev_state = cur_state
        if show_status:
            yield ['status']
            for src in nodes:
                msgs_info_str = 'msgs {}:'.format(src)
                for dst in nodes:
                    if src != dst:
                        msgs_info_str += ' {}({})'.format(dst, len(msg[src][dst]))
                yield ['#', msgs_info_str]
            # yield ['compare', 'net']
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
        for i in traces:
            try:
                ' '.join(i)
            except Exception as e:
                print(i)
                raise e
        f.write('\n'.join(' '.join(i) for i in traces))


if __name__ == '__main__':
    args = parse_args()
    read_config()
    copy_config_file(args.config, not args.in_place)
    gen_trace()

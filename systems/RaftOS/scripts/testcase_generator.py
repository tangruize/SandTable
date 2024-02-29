import sys
import os
import jq
import argparse
import shutil
import signal
import json

show_status=True

def set_path():
    def dirname_level_up(name, level):
        for _ in range(level):
            name = os.path.dirname(name)
        return name

    script_dir = os.path.dirname(os.path.realpath(__file__))
    deps_dir = os.path.join(dirname_level_up(script_dir, 3), 'scripts')
    sys.path.append(deps_dir)

set_path()

from trace_reader import TraceReader

def sigint_handler(signum, frame):
    print('TC-Gen Caught SIGINT, Ctrl+C again to exit')
    signal.signal(signal.SIGINT, signal.SIG_DFL)


signal.signal(signal.SIGINT, sigint_handler)

default_path = '/root/sandtable/systems/RaftOS/raftos'
default_config = 'config.txt'
default_output = 'traces.txt'
default_conn_fd = 126
default_node_port = 10200
default_debug = False
nodes = dict()
addr_map = dict()
node_port = None


def parse_args():
    parser = argparse.ArgumentParser(description="Test case generator for PySyncObj")
    parser.add_argument(dest='trace_file', action='store', help='Trace file')
    parser.add_argument('-c', dest='config', action='store', required=True, help='Config file',
                        default=default_config)
    parser.add_argument('-o', dest='output', action='store', required=False, help='Output trace file',
                        default=default_output)
    parser.add_argument('-p', dest='path', action='store', required=False, help='PySyncObj path',
                        default=default_path)
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
        os.mkdir(test_case_dir, mode=0o755)
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
                        fake_ip = ip.replace(k, v)
                        nodes[name] = fake_ip
                        # add addr_map
                        addr_map["{}".format(ip)] = "{}".format(fake_ip)
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


# TO IMPROVE: {others} can be simplified to all nodes. No need to exclude self node from {others}
def gen_test_code(config_file, testcase_in_parent_dir):
    try:
        if testcase_in_parent_dir:
            os.symlink(os.path.dirname(config_file), 'config')
        else:
            shutil.copy2(config_file, os.path.join('..' if testcase_in_parent_dir else '.', os.path.basename(config_file)))
    except:
        pass
    if check_test_code_is_generated(config_file, testcase_in_parent_dir):
        return
    test_case_template = '''import sys
sys.path.insert(1, '{path}')
import asyncio
from datetime import datetime
import random
import socket
import raftos
import os
import struct
import threading

lock = threading.Lock()

node = '{n1}'
cluster = [ {others}]
net_address_map = {addr_map}
nodes = {nodes}

raftos.configure({{'log_path': './', 
    'serializer': raftos.serializers.JSONSerializer, 
    'net_address_map' : net_address_map}})

global server
global data
global res

data = None
server = None
restart = None


loop = asyncio.new_event_loop()
asyncio.set_event_loop(loop)

loop.set_debug(True)

data_id = raftos.Replicated(name='data_id')

async def regist_node():
    hostaddr = socket.gethostbyname(socket.gethostname())
    hostaddr+=":{node_port}"
    server1 = await raftos.register(hostaddr, cluster=cluster, loop = loop)
    return server1

def reply(value):
    value = str(value).encode()
    length = struct.pack('!i', len(value))
    os.write({conn_fd}, length + value)


def getVariable(v):
    global server
    if 'raftState' == v:
        if isinstance(server.state.state, raftos.state.Leader):
            return 'Leader'
        elif isinstance(server.state.state, raftos.state.Candidate):
            return 'Candidate'
        elif isinstance(server.state.state, raftos.state.Follower):
            return 'Follower'
    elif 'currentTerm' == v:
        return str(server.state.storage.term)
    elif 'votedFor' == v:
        return str(server.state.storage.voted_for)
    elif 'log' == v:
        print(type(server.state.log.read()))
        log_cache = list(map(lambda t: (t['term'], t['command']['data_id']), server.state.log.read()))             
        result = [(value[0], index + 1, value[1]) for index, value in enumerate(log_cache)]
        return result
    elif 'commitIndex' == v:
        return str(server.state.log.commit_index)
    elif v in {{'match_index', 'next_index'}}:
        result2 = dict()
        result = eval('server.state.log.' + v)
        for i,j in result.items():
            i = str(i)
            result2[nodes[i] if i in nodes else i] = j
        return dict(sorted(result2.items()))

def read_execute():
    global res
    global data
    for line in sys.stdin:
        try:
            # data = "123"
            exec(line, globals())
        except Exception as e:
            print('Error: triggered an exception', file=sys.stderr)
            os.write(126, b'1')
            raise e
        reply(res)


async def main():
    global server
    server = await regist_node()
    global node
    global res
    global data
    global restart
    
    input_thread = threading.Thread(target=read_execute)
    input_thread.start()
  
    while True:
        print('in main, data', data)
        leader_id = raftos.get_leader()
        print('leader id:' ,leader_id)
        if leader_id == node and data is not None:
            local_data = data
            print('in main, we set data', local_data)
            await data_id.set(local_data)
            data = None
        elif restart is not None:
            server.state.start()
            restart = None
        else :
            await asyncio.sleep(0.1)
    
    # Run the event loop indefinitely
    await asyncio.Event().wait()
        
        
loop.run_until_complete(main()) 
    
'''
    udp_nodes = {}
    for k,v in nodes.items():
        udp_nodes["{}".format(v)] = k
    format_dict = {'path': args.path, 'conn_fd': args.conn_fd, 'node_port': node_port, 'nodes': str(udp_nodes), 'addr_map': str(addr_map)}
    others = ''
    for j in range(len(nodes)-1):
        others += "'{n" + str(j+2) + "}', "
    
    others = others[:-2]
    test_case_real_template = test_case_template.replace('{others}', others)
    node_names = list(nodes.keys())
    node_names.sort()
    combs = list()
    for self_node in node_names:
        comb_dict = {'self_node': self_node, 'n1': nodes[self_node]}
        for j, v in enumerate(set(node_names) - {self_node}):
            comb_dict['n' + str(j+2)] = nodes[v]
        combs.append(comb_dict)
    test_cases = {}
    for j in combs:
        test_cases[j['self_node']] = test_case_real_template.format(**format_dict, **j)
    for name, test_code in test_cases.items():
        with open(os.path.join('config' if testcase_in_parent_dir else '.', name + '.py'), 'w') as f:
            f.write(test_code)


def yield_trace(states):
    model_value = ''
    # model_value_replace = {"Follower": "0", "Candidate": "1", "Leader": "2"}
    # for k,v in nodes.items():
    #     model_value_replace["TCPNode('{}:{}')".format(v, node_port)] = k
    def get_converted_model_value(n, model_var_name):
        nonlocal model_value
        if model_var_name == 'log':
            model_value = list(map(lambda t: tuple(t.values()), model_value))
        elif model_var_name in {'nextIndex', 'matchIndex'}:
            if n in model_value:
                model_value.pop(n)
        return str(model_value)
    def compare(n, code_var_name, model_var_name, no_compare=False):
        nonlocal model_value
        yield ['execute', n, 'res=getVariable("{}")'.format(code_var_name)]
        # yield ['execute', n, 'print(res)']
        model_value = cur_state[model_var_name][n]
        yield ['#', 'variable', model_var_name, n, get_converted_model_value(n, model_var_name)]
        if not no_compare:
            yield ['compare', 'variable']
        else:
            yield ['compare', 'none']
    def do_tick(n, is_compare=True):
        nonlocal model_value
        yield from compare(n, 'commitIndex', 'commitIndex')
        yield from compare(n, 'currentTerm', 'currentTerm')
        yield from compare(n, 'log', 'log')
        yield from compare(n, 'raftState', 'raftState')
        if model_value == "Leader":  # leader
            yield from compare(n, 'next_index', 'nextIndex')
            yield from compare(n, 'match_index', 'matchIndex')
    def deliver(msg_num, dst, src):
        nonlocal need_tick_twice
        yield ['deliver', str(msg_num)]
        yield ['#', 'deliver', dst, 'to', src]
        yield ['nop']
        yield from do_tick(src)
    jq_trace = jq.compile('.[].netcmd')
    jq_msgs = jq.compile('.[].msgs')
    states_counter = 0
    need_tick_twice = False
    for i, msg, cur_state in zip(jq_trace.input(states), jq_msgs.input(states), states):
        states_counter += 1
        if len(i) > 1:
            comment = i[0]
            netcmd = i[1]
            cmd, *parameters = netcmd
            for i in range(len(comment)):
                if not isinstance(comment[i],str):
                    comment[i] = str(comment[i])
            # here have int
            yield ['#', '[' + str(states_counter) + ']'] + comment
            # if 'HandleMsgAER success' in ' '.join(comment):
            #     need_tick_twice = True  # the second round increases commitIndex
            # cmd_str = json.dumps(netcmd)
            # cmd_str[-1] = '[' + cmd_str[-1] + ']'
            yield ['#', str(json.dumps(netcmd))]
            yield ['sleep', '50']
            if comment[0] == 'Restart':
                yield ['execute', comment[1], "restart = True"]
                yield ['intercept', comment[1], 'inc_time_ms', '100']  # > 0.1s
                yield ['nop']
            
            if cmd == 'msg_del':  # recv msg (deliver to node)
                # yield ['deliver', parameters[0], parameters[1]]
                yield from deliver(parameters[0], parameters[1], parameters[2])
            elif cmd == 'msg_add':  # send msg (enqueued in controller)
                assert False
                pass  # not used
            elif cmd == 'msg_add_dropped':  # send msg but dropped due to partition
                assert False
                pass  # not used
            elif cmd == 'msg_reply':  # recv (deliver) msg and send (enqueue) msg
                # yield ['deliver', parameters[1], parameters[0]]
                yield from deliver(parameters[0], parameters[1], parameters[2])
            elif cmd == 'msg_drop':  # drop message
                yield ['drop', str(parameters[0])]
            elif cmd == 'msg_dup':  # duplicate message
                yield ['duplicate', str(parameters[0])]
            elif cmd == 'msg_reply_dropped':  # reply but dropped
                # yield ['deliver', parameters[1], parameters[0]]
                yield from deliver(parameters[0], parameters[1], parameters[2])
            elif cmd == 'msg_batch_add':  # batch send msgs
                if comment[0] == 'ElectionTimeout':
                    yield ['intercept', comment[1], 'inc_time_ms', '90000']  # > 90s
                    yield ['nop']
                elif comment[0] == 'SendAppendEntries':
                    yield ['intercept', comment[1], 'inc_time_ms', '6500']  # > 6s
                    yield ['nop']
                elif comment[0] == 'ClientRequest':
                    yield ['execute', comment[1], "data = '{}'".format(comment[2])]
                    yield ['intercept', comment[1], 'inc_time_ms', '100']  # > 0.1s
                    yield ['nop']
                
                yield from do_tick(comment[1])
            elif cmd == 'msg_batch_add_reply':  # recv msg and batch send msgs
                # yield ['deliver', parameters[1], parameters[0]]
                yield from deliver(parameters[0], parameters[1], parameters[2])
        else:
            yield ['init', str(i[0][1])]
            for j in nodes:
                # yield ['intercept', j, "inc_time_ms", '1000']
                yield from do_tick(j)
            # yield ['wait-init', str(i[0][1])]
            # yield ['deliver-all', str(len(nodes))]
            # for j in nodes:
            #     yield ['loop', 'execute', j, 'res=connectedToAll()']
        if show_status:
            yield ['status']
            try :
                my_msg_show = 'msgs :'
                for one in msg:
                    my_msg_show += ' ' + str(one['seq']) + ' '+  str(one['src']) +' -> ' + str(one['dst'])            
                msgs_info_str = 'msgs :' + "\'"+str(json.dumps(msg)) + "\'"
            except Exception as e:
                raise e
            yield ['#', 'for read', my_msg_show]
            yield ['#', msgs_info_str]
            # yield ['compare', 'net']
    # for i in nodes:
    #     yield ['execute', i, "print(data_id.get(1))"]
    eprint("Finish write:", args.output)


def gen_trace():
    tr = TraceReader(True)
    try:
        os.symlink(args.trace_file, 'tlc_trace.txt')
    except:
        pass
    states = list(tr.trace_reader(args.trace_file))
    eprint('Read states:', len(states))
    traces = list(yield_trace(states))
    for i in traces:
        for j in i:
            if isinstance(j, int):
                print("i:", i)
                print(j, "is int")
    with open('traces.txt', 'w') as f:
        f.write('\n'.join(' '.join(i) for i in traces))


if __name__ == '__main__':
    args = parse_args()
    read_config()
    gen_test_code(args.config, not args.in_place)
    gen_trace()

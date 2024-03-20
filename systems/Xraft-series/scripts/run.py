import sys
import os
import signal
import argparse
import jq
import json
import inotify.adapters
import time
from datetime import datetime
from multiprocessing import Pool, Value
import subprocess

disable_check = False

script_dir = os.path.dirname(__file__)
deps_dir = script_dir
for _ in range(3):
    deps_dir = os.path.dirname(deps_dir)
deps_dir = os.path.join(deps_dir, 'scripts')
sys.path.append(deps_dir)
# print(sys.path)


def join_script_path(script_fn):
    return os.path.join(script_dir, script_fn)


generator_script = join_script_path('testcase_generator.py')
gen_config_script_lxd = join_script_path('gen_3_config_lxd.sh')
gen_config_script_docker = join_script_path('gen_3_config.sh')
check_script_lxd = join_script_path('start-lxd.sh')
check_script_docker = join_script_path('start.sh')
num_servers = 3

if os.path.exists('/.dockerenv'):
    check_script = check_script_docker
    gen_config_script = gen_config_script_docker
    subnet_prefix = '1'
else:
    check_script = check_script_lxd
    gen_config_script = gen_config_script_lxd
    subnet_prefix = '2'


from trace_reader import TraceReader
from branch_counter import counter, jq_cmd_str, jq_inv_str


def _sigint_handler():
    signal.signal(signal.SIGINT, signal.SIG_DFL)
    print('Caught signal, exiting...')
    for proc in processes:
        proc.terminate()
    print_progress(False)
    print_unreached_branches(counter)
    print_inv_violated_files()
    for proc in processes:
        proc.join()
    exit(0)

def sigint_handler(signum, frame):
    _sigint_handler()


signal.signal(signal.SIGINT, sigint_handler)


def is_trace_file(fn):
    return fn.startswith("trace_") and not fn.endswith(".dir")

tr = TraceReader()
processed_files = 0
jq_cmd = jq.compile(jq_cmd_str)
jq_inv = jq.compile(jq_inv_str)
# jq_length = jq.compile('length')
inv_violated = False
inv_violated_files = {}
total_states = 0
test_case_dir = 'testcase{}'.format(datetime.now().strftime("_%Y-%m-%d_%H-%M-%S"))

n_process = 1

def init_worker():
    def handler(signum, frame):
        print('Pool: process killed by signal:', signum)
        exit(1)
    signal.signal(signal.SIGINT, handler)
    signal.signal(signal.SIGTERM, handler)

config_file_list = []

def gen_config():
    global config_file_list
    for i in range(n_process):
        cur_config_dir = os.path.join(test_case_dir, str(i))
        cur_config = os.path.join(cur_config_dir, 'config.txt')
        os.makedirs(cur_config_dir, exist_ok=True)
        # os.system('bash {} {} 10.{}.{}.0/24 {}'.format(gen_config_script, num_servers, subnet_prefix, i, cur_config))
        ret = subprocess.run(['bash', gen_config_script, str(num_servers), '10.{}.{}.0/24'.format(subnet_prefix, i), cur_config], shell=False, check=False)
        if ret.returncode < 0:
            _sigint_handler()
        config_file_list.append(cur_config)

def run_testcase_worker(fn):
    # print('env -u TMUX bash {} {}'.format(check_script, os.path.realpath(os.path.join('.', test_case_dir, fn+'.dir'))))
    os.system('env -u TMUX bash {} {}'.format(check_script, os.path.realpath(os.path.join('.', test_case_dir, fn+'.dir'))))

def run_testcase(fn):
    slot = processed_files % n_process
    processes[slot].apply_async(run_testcase_worker, (fn,))

# from testcase_generator import gen_trace
def process_file(fn):
    global processed_files, inv_violated, total_states
    processed_files += 1
    states = list(tr.trace_reader(fn))
    for i in jq_cmd.input(states):
        level_1 = counter[i[0]]
        if isinstance(level_1, int):
            counter[i[0]] += 1
        else:
            level_1[i[1]] += 1
    if not all(jq_inv.input(states)):
        # inv_violated_files.append(fn)
        inv_violated = True
        inv_violated_files[fn] = list(jq.compile('.[-1] | .inv | .[]').input(states))
    # total_states += jq_length.input(states).all()[0]
    total_states += len(states)
    # gen_trace(states)
    if fn == 'MC.out' and not inv_violated:
        return
    # os.system('python3 {} -I {} -c {} {}'.format(generator_script, test_case_dir, config_file_list[processed_files%n_process], fn))
    ret = subprocess.run(['python3', generator_script, '-I', test_case_dir, '-c', config_file_list[processed_files%n_process], fn], shell=False, check=False)
    if ret.returncode < 0:
        _sigint_handler()
    # print(os.path.realpath(os.path.join('.', test_case_dir, fn+'.dir')))
    # os.system('bash {} {}'.format(check_script, os.path.realpath(os.path.join('.', test_case_dir, fn+'.dir'))))
    if (not disable_check) and ret.returncode == 0:
        run_testcase(fn)

def print_inv_violated_files():
    if inv_violated_files:
        print('# Invariants violated files: ')
        print(json.dumps(inv_violated_files, indent=4))

prev_time = 0
period = 5
def print_progress(wait_period=True):
    global prev_time, period
    current_time = time.time()
    if current_time - prev_time >= period or not wait_period:
        print('# Total states:', total_states)
        cache = 0
        for i in processes:
            cache += len(i._cache)
        run_files = processed_files - cache
        print('# Run testcases: {}/{} ({})'.format(run_files, processed_files, (run_files + 1) / (processed_files + 1)))
        print("# COVERAGE of {} traces".format(processed_files))
        print(json.dumps(counter, indent=4))
        prev_time = current_time
        print_inv_violated_files()

def print_unreached_branches(d, keys=None):
    tmp_keys = [] if keys is None else keys
    if keys is None:
        print("# Unreached branches")
    for k,v in d.items():
        if isinstance(v, int):
            if v == 0:
                print(tmp_keys + [k])
        else:
            print_unreached_branches(v, tmp_keys + [k])


use_inotify=True
trace_dir = ''


def process_dir():
    global trace_dir
    gen_config()
    finish_file = "MC.out"
    if use_inotify:
        i = inotify.adapters.Inotify()
        i.add_watch('.')
        while True:
            event = None

            for event in i.event_gen(yield_nones=False, timeout_s=1):
                (_, type_names, _, filename) = event
                event = None
                if type_names == ['IN_CLOSE_WRITE']:
                    if not is_trace_file(filename) and filename != finish_file:
                        continue
                    process_file(filename)
                    print_progress()
                    if filename == finish_file:
                        event = ""
                        break
            print_progress()
            if event is not None:
                break
    else:
        file_list = [i for i in os.listdir() if is_trace_file(i) or i == finish_file]
        for i in file_list:
            process_file(i)
            print_progress()


def parse_args():
    global n_process, num_servers, disable_check, use_inotify, trace_dir
    parser = argparse.ArgumentParser(description='Convert TLA+ trace to test cases and run them!')
    parser.add_argument(dest='trace_dir', action='store', help='TLA trace dir')
    parser.add_argument('-p', dest='proc_num', action='store', type=int, required=False,
                        help='Number of parallel running test case')
    parser.add_argument('-s', dest='server_num', action='store', type=int, required=False,
                        help='Number of servers')
    parser.add_argument('-d', dest='disable_check', action='store_true', required=False,
                        help='Disable check')
    parser.add_argument('-i', dest='iterate_dir', action='store_true', required=False,
                        help='Iterate dir instead of use inotify')
    args = parser.parse_args()
    if args.proc_num:
        n_process = args.proc_num
    if args.server_num:
        num_servers = args.server_num
    if args.disable_check:
        disable_check = True
    if args.iterate_dir:
        use_inotify = False
    trace_dir = args.trace_dir
    os.chdir(trace_dir)


if __name__ == '__main__':
    # iterate_dir(False)
    parse_args()
    processes = []
    for _ in range(n_process):
        processes.append(Pool(1, init_worker))
    process_dir()
    for proc in processes:
        proc.close()
        proc.join()
    print_unreached_branches(counter)
    print_inv_violated_files()

import sys
import os
import signal

script_dir = os.path.dirname(__file__)
deps_dir = os.path.join(os.path.dirname(os.path.dirname(script_dir)), 'deps')
generator_script = os.path.join(script_dir, 'testcase_generator.py')
config_file = os.path.join(script_dir, 'config.txt')
gen_config_script_lxd = os.path.join(os.path.dirname(script_dir), 'configuration', 'gen_3_config_lxd.sh')
gen_config_script_docker = os.path.join(os.path.dirname(script_dir), 'configuration', 'gen_3_config.sh')
check_script_lxd = os.path.join(os.path.dirname(script_dir), 'run-testcase', 'start-lxd.sh')
check_script_docker = os.path.join(os.path.dirname(script_dir), 'run-testcase', 'start.sh')
num_servers = 3

if os.path.exists('/.dockerenv'):
    check_script = check_script_docker
    gen_config_script = gen_config_script_docker
    subnet_prefix = '1'
else:
    check_script = check_script_lxd
    gen_config_script = gen_config_script_lxd
    subnet_prefix = '2'

sys.path.append(os.path.join(deps_dir, 'tlc-cmd'))
# print(sys.path)

from trace_reader import TraceReader

import jq
import json
import inotify.adapters
import time
from datetime import datetime
from multiprocessing import Pool, Value

def sigint_handler(signum, frame):
    print('Caught SIGINT, Ctrl+C again to exit')
    signal.signal(signal.SIGINT, signal.SIG_DFL)


signal.signal(signal.SIGINT, sigint_handler)


counter = {
    "init": 0,
    "SendAppendEntries": 0,
    "HandleMsgRV": {
        "voted": 0,
        "not-voted": 0
    },
    "HandleMsgRVR": {
        "become-leader-and-send-append-entries": 0,
        "not-quorum": 0,
        "not-candidate-or-term-not-equal": 0
    },
    "HandleMsgAE": {
        "term-is-smaller": 0,
        "no-prevEntries": 0,
        "term-mismatch": 0,
        "success": 0
    },
    "HandleMsgNNI": {
        "reset": 0,
        "success": 0,
        "not-leader": 0
    },
    "ElectionTimeout": 0,
    "DoNetworkPartition": 0,
    "DoNetworkCure": 0,
    "ClientRequest": 0
}

def is_trace_file(fn):
    return fn.startswith("trace_") and not fn.endswith(".dir")

tr = TraceReader()
processed_files = 0
jq_cmd = jq.compile('.[] | .netcmd | .[0] | .[0:2]')
jq_inv = jq.compile('.[] | .inv | .[]')
# jq_length = jq.compile('length')
inv_violated = False
inv_violated_files = {}
total_states = 0
test_case_dir = 'testcase{}'.format(datetime.now().strftime("_%Y-%m-%d_%H-%M-%S"))

n_process = 8

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
        os.system('bash {} {} 10.{}.{}.0/24 {}'.format(gen_config_script, num_servers, subnet_prefix, i, cur_config))
        config_file_list.append(cur_config)

def run_testcase_worker(fn):
    os.system('env -u TMUX bash {} {}'.format(check_script, os.path.realpath(os.path.join('.', test_case_dir, fn+'.dir'))))

def run_testcase(fn):
    slot = processed_files % n_process
    processes[slot].apply_async(run_testcase_worker, (fn,))

from testcase_generator import gen_trace
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
    os.system('python3 {} -I {} -c {} {}'.format(generator_script, test_case_dir, config_file_list[processed_files%n_process], fn))
    # print(os.path.realpath(os.path.join('.', test_case_dir, fn+'.dir')))
    # os.system('bash {} {}'.format(check_script, os.path.realpath(os.path.join('.', test_case_dir, fn+'.dir'))))
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

def iterate_dir(use_inotify=True):
    trace_dir = sys.argv[1]
    os.chdir(trace_dir)
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

#TEST
# process_file('/mnt/data/GitHub/Work/PySyncObjTLA/model/ae_2022-09-26_20-42-23_1/trace_0_0')
# print_progress(False)

if __name__ == '__main__':
    # iterate_dir(False)
    processes = []
    for _ in range(n_process):
        processes.append(Pool(1, init_worker))
    iterate_dir()
    print_unreached_branches(counter)
    print_inv_violated_files()
    for proc in processes:
        proc.close()
        proc.join()
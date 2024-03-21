#!/usr/bin/python3
# -*- coding: UTF-8 -*-

import sys
import re
import os
import subprocess
import argparse
import signal

from collections import OrderedDict
from configparser import ConfigParser
from itertools import chain, zip_longest, product
from shutil import copy2
from datetime import datetime
from datetime import timedelta
from io import StringIO
from collections.abc import Mapping

debug = True

wrapper_out_file=None

def xprint(*args, **kwargs):
    if wrapper_out_file:
        print(*args, **kwargs, file=wrapper_out_file, flush=True)
    print(*args, **kwargs, flush=True)

def eprint(*args, **kwargs):
    if wrapper_out_file:
        print(*args, **kwargs, file=wrapper_out_file, flush=True)
    print(*args, **kwargs, file=sys.stderr, flush=True)

class PrintTable:
    """Print CSV/Markdown table"""

    @classmethod
    def _print_table(cls, table, title=None, file=sys.stdout, sep=',', wrap='', default=''):
        def _w(string): return '{} {} {}'.format(wrap, string, wrap).strip()
        def _p(string): return string if wrap else '"{}"'.format(string.replace('"','""'))
        def _f(it):     return filter(lambda x: x is not None, it)
        def _t(string): return _p(title[string]) if string in title else None
        def _v(k, d):
            if k not in d:
                return _p(str(default))
            return _p(str(d[k])) if k in title else None

        table = list(table.values()) if isinstance(table, Mapping) else list(table)
        if title is None:
            title = dict(zip(table[0].keys(), table[0].keys()))
        xprint(_w(sep.join(_f(map(lambda k: _t(k), title.keys())))), file=file)
        if wrap:
            xprint(_w(sep.join(_f(map(lambda k:  '---' if _t(k) else None, title.keys())))), file=file)
        for i in table:
            xprint(_w(sep.join(_f(map(lambda kd: _v(*kd), ((k, i) for k in title.keys()))))), file=file)

    @classmethod
    def print_csv_table(cls, table, title=None, file=sys.stdout, tab=False, default=''):
        cls._print_table(table, title, file=file, sep='\t' if tab else ',', default=default)

    @classmethod
    def print_md_table(cls, table, title=None, file=sys.stdout, default=''):
        cls._print_table(table, title, file=file, sep=' | ', wrap='|', default=default)

    @classmethod
    def print_table(cls, table, title=None, filename='', default=''):
        if not filename:
            cls.print_csv_table(table, title, tab=True, default=default)
        else:
            if filename.endswith('.md'):
                with open(filename, 'w') as out:
                    cls.print_md_table(table, title, out, default=default)
            else:
                with open(filename, 'w', encoding='utf-8-sig') as out:
                    cls.print_csv_table(table, title, out, default=default)


class Summary:
    """Output summary table"""

    _title_list = ['Diameter', 'States Found', 'Distinct States', 'Queue Size', 'Start Time', 'End Time', 'Duration',
                   'Exit Status', 'Warnings', 'Errors']
    _title_list_simulation = ['Traces', 'States Found', 'Start Time', 'End Time', 'Duration',
                              'Exit Status', 'Warnings', 'Errors']

    def __init__(self):
        self.batch = []
        self.current = None
        self._finished = True

    def init_title(self, is_simulation=False):
        if self._finished:
            self.new()
        titles = self._title_list if not is_simulation else self._title_list_simulation
        for t in titles:
            if t not in self.current:
                self.current[t] = None

    def add_option(self, opt, value):
        v = value.replace('[model value]', '').replace('<symmetrical>', '').strip()
        if not v:
            v = value
        self.add_info(opt, v, force=True)
        if v.startswith('{'):
            n = len(v.split(','))
            self.add_info('n {}'.format(opt), n, force=True)

    def add_info(self, name, value, force=False):
        if self._finished:
            self.new()
        name = name.title()
        if force or name in self.current:
            self.current[name] = value

    def new(self):
        self.batch.append(OrderedDict())
        self.current = self.batch[-1]
        self.current['No.'] = len(self.batch)
        self._finished = False

    def finish_current(self):
        self._finished = True

    def _get_longest_title(self):
        title_list = []
        for task in self.batch:
            tmp_list = list(task.keys())
            if len(title_list) < len(tmp_list):
                title_list = tmp_list
        return title_list

    def __str__(self):
        if self.current is None:
            return ''
        lines = ['\t'.join(self._get_longest_title())]
        for task in self.batch:
            lines.append('\t'.join(str(i).replace('\n', ' ') for i in task.values()))
        return '\n'.join(lines)
    
    def print_to_file(self, file):
        title = self._get_longest_title()
        title = dict(zip(title, title))
        PrintTable.print_table(self.batch, title, file)


class BatchConfig:
    """Yield TLCConfigFile cfg files"""

    def __init__(self, cfg, summary=None):
        self.dup_option_info = OrderedDict()
        self.cfg_content = []
        self.summary = summary
        if not hasattr(cfg, 'read'):
            cfg_file = open(cfg, 'r')
        else:
            cfg_file = cfg
        self._parse_cfg(cfg_file)
        cfg_file.close()

    def _parse_cfg(self, cfg_file):
        pre_opt_kv = ['', '']
        pre_no = -1

        def rm_non_dup_option():
            if pre_no in self.dup_option_info:
                if len(self.dup_option_info[pre_no]) <= 1:
                    line = self.dup_option_info.pop(pre_no)
                    self.cfg_content[pre_no] = line[0] + '\n'
                else:
                    self.dup_option_info[pre_no] = [
                        i for i in self.dup_option_info[pre_no] if "SHOW_IN_TABLE" != i.split(':', 1)[1].strip()]

        for no, line in enumerate(cfg_file):
            self.cfg_content.append(line)
            line = line.rstrip()
            if len(line) == 0 or line[0] in '#;[':
                continue
            if line[0] in ' \t':
                if pre_no != -1:
                    self.cfg_content[-1] = ''
                    self.dup_option_info[pre_no][-1] = '{}\n{}'.format(self.dup_option_info[pre_no][-1], line)
                continue
            opt_kv = line.split(':', 1)
            if len(opt_kv) != 2:
                continue
            if opt_kv[0] == pre_opt_kv[0]:
                self.dup_option_info[pre_no].append(line)
                self.cfg_content[-1] = ''
            else:
                rm_non_dup_option()
                self.dup_option_info[no] = [line]
                pre_no = no
            pre_opt_kv = opt_kv
        rm_non_dup_option()

    def get(self):
        """yield cfg StringIO"""
        keys = list(self.dup_option_info.keys())
        values = list(self.dup_option_info.values())
        for comb in product(*values):
            for i, no in enumerate(keys):
                self.cfg_content[no] = comb[i] + '\n'
                opt, value = comb[i].split(':', 1)
                if self.summary:
                    self.summary.add_option(opt.strip(), value.strip())
            yield comb, StringIO(''.join(self.cfg_content))


class TLCConfigFile:
    """generate TLC config file: MC.cfg and MC.tla"""
    model_sym_pat = re.compile(r'\[model value]<symmetrical>{(.*)}')
    model_pat = re.compile(r'\[model value]{(.*)}')
    tag = '\\* Generated by ' + os.path.basename(__file__)

    def __init__(self, cfg, output_cfg_fn, output_tla_fn, output_tla_constants_fn=None, target_tla_file=None):
        self.cfg = cfg
        self.output_cfg_fn = output_cfg_fn
        self.output_tla_fn = output_tla_fn

        if output_tla_constants_fn and not target_tla_file:
            eprint('Warning:', 'both output_tla_constants_fn and target_tla_file must be set')
            output_tla_constants_fn = None

        self.output_tla_constants_fn = output_tla_constants_fn
        self.target_tla_file = target_tla_file
        if self.output_tla_constants_fn:
            self.extends_string = self._get_extends_str(self.target_tla_file)
        else:
            self.extends_string = ''
        self.top_module = re.sub(r'.tla$', '', os.path.basename(cfg.get('options', 'target')))
        self.output_cfg = []
        self.output_tla_options = []
        self.output_tla_constants = []
        if not output_tla_constants_fn:
            self.output_tla_constants = self.output_tla_options
        self.parse()

    def _get_extends_str(self, target_tla_fn):
        """get 'x, y, z' in tla file 'EXTENDS x, y, z'"""
        with open(target_tla_fn) as f:
            for line in f:
                line = line.strip()
                if line.startswith('EXTENDS'):
                    _, e = line.split(' ', 1)
                    if 'TLC' in e:
                        return e
                    else:
                        return e + ', TLC'
    
    def _set_extends_str(self, more):
        if not self.target_tla_file:
            return
        with open(self.target_tla_file) as f:
            lines = f.readlines()
        module_idx = -1
        find_extends = False
        for i, line in enumerate(lines):
            if module_idx == -1 and 'MODULE' in line:
                module_idx = i
            if line.strip().startswith('EXTENDS'):
                if more not in line:
                    lines[i] = line.rstrip() + ', ' + more + '\n'
                find_extends = True
                break
        if not find_extends and module_idx != -1:
            lines.insert(module_idx + 1, 'EXTENDS ' + more + '\n')
        with open(self.target_tla_file, 'w') as f:
            f.writelines(lines)

    def _add_behavior(self, specifier, prefix, value):
        behavior_name = '{}'.format(prefix)
        behavior_value = '{} ==\n{}'.format(behavior_name, value)
        self.output_cfg.append('{}\n{}'.format(specifier, behavior_name))
        self.output_tla_options.append(behavior_value)

    def _parse_behavior(self):
        """parse behavior section"""
        if 'behavior' in self.cfg:
            behavior = self.cfg['behavior']
            init_predicate = behavior.get('init')
            next_state = behavior.get('next')
            temporal_formula = behavior.get('temporal formula')
            if (init_predicate or next_state) and (not init_predicate or not next_state or temporal_formula):
                raise ValueError('[behavior] choose one or none: "init/next" **OR** "temporal formula"')
            if temporal_formula:
                self._add_behavior('SPECIFICATION', 'spec', temporal_formula)
            else:
                self._add_behavior('INIT', 'init', init_predicate)
                self._add_behavior('NEXT', 'next', next_state)

    def _add_specifications(self, keyword, specifier, prefix):
        """invariants and properties share the same parser"""
        if keyword in self.cfg:
            spec = self.cfg[keyword]
            spec_names = '\n'.join('{}_{}'.format(prefix, i) for i in spec)
            if spec_names != '':
                self.output_cfg.append('{}\n{}'.format(specifier, spec_names))
                spec_values = '\n'.join('{}_{} ==\n{}'.format(prefix, i, spec[i]) for i in spec)
                self.output_tla_options.append(spec_values)

    def _parse_invariants(self):
        """parse invariants section"""
        self._add_specifications('invariants', 'INVARIANT', 'inv')

    def _parse_properties(self):
        """parse properties section"""
        self._add_specifications('properties', 'PROPERTY', 'prop')

    def _parse_state_constraint(self):
        """parse state constraint section"""
        self._add_specifications('state constraint', 'CONSTRAINT', 'constr')

    def _parse_action_constraint(self):
        """parse action constraint section"""
        self._add_specifications('action constraint', 'ACTION_CONSTRAINT', 'action_constr')

    def _parse_constants(self, keyword='constants', prefix='const'):
        """parse constants section"""
        if keyword in self.cfg:
            symmetrical = []
            constants = self.cfg[keyword]
            for name in constants:
                value = constants[name]
                is_model_value = False
                is_symmetrical = False
                if self.model_sym_pat.match(value):
                    is_model_value = True
                    value = self.model_sym_pat.match(value).groups()[0].replace(' ', '').split(',')
                    if len(value) <= 1:
                        eprint('Warning: "{}: {}": <symmetrical> ignored'.format(name, constants[name]))
                    else:
                        is_symmetrical = True
                elif self.model_pat.match(value):
                    is_model_value = True
                    value = self.model_pat.match(value).groups()[0].replace(' ', '').split(',')
                elif value == '[model value]':
                    is_model_value = True
                    value = name
                if is_model_value:
                    if isinstance(value, list):  # set of model values
                        model_val = '\n'.join('{} = {}'.format(i, i) for i in value)
                        cfg_str = 'CONSTANTS\n{}\nCONSTANT\n{} <- const_{}'.format(model_val, name, name)
                        model_val = ', '.join(i for i in value)
                        tla_str = 'CONSTANTS\n{}\nconst_{} ==\n{{{}}}'.format(model_val, name, model_val)
                        if is_symmetrical:  # symmetry set
                            # cfg_str = '{}\nSYMMETRY symm_{}'.format(cfg_str, name)
                            # tla_str = '{}\nsymm_{} ==\nPermutations(const_{})'.format(tla_str, name, name)
                            symmetrical.append('Permutations(const_{})'.format(name))
                    else:  # model value
                        cfg_str = 'CONSTANT {} = {}'.format(name, value)
                        tla_str = None
                else:  # ordinary assignment
                    cfg_str = 'CONSTANT\n{} <- {}_{}'.format(name, prefix, name)
                    tla_str = '{}_{} == \n{}'.format(prefix, name, value)
                self.output_cfg.append(cfg_str)
                self.output_tla_constants.append(tla_str)
            if symmetrical:
                self.output_cfg.append('SYMMETRY symm_{}'.format(len(symmetrical)))
                self.output_tla_constants.append(
                    'symm_{} ==\n{}'.format(len(symmetrical), ' \\union '.join(symmetrical)))

    def _parse_override(self):
        """parse override section"""
        self._parse_constants(keyword='override', prefix='over')

    def _parse_const_expr(self):
        """parse const expr section"""
        if 'const expr' in self.cfg:
            const_expr = self.cfg.get('const expr', 'expr', fallback=None)
            if const_expr:
                self.output_cfg.append(None)
                val = 'const_expr'
                self.output_tla_options.append(
                    '{} ==\n{}\nASSUME PrintT(<<"$!@$!@$!@$!@$!",{}>>)'.format(val, const_expr, val))

    def _parse_additional_definitions(self):
        """parse additional definitions section"""
        if 'additional definitions' in self.cfg:
            self.output_cfg.append(None)
            spec = self.cfg['additional definitions']
            spec_values = '\n'.join(spec[i] for i in spec)
            self.output_tla_options.append(spec_values)

    def _parse_alias(self):
        """parse alias section"""
        self._add_specifications('alias', 'ALIAS', 'alias')
        # if 'alias' in self.cfg:
        #     self.output_cfg.append(None)
        #     spec = self.cfg['alias']
        #     spec_values = '\n'.join(spec[i] for i in spec)
        #     self.output_cfg.append('{}\n{}'.format('ALIAS', spec_values))

    def parse(self):
        self.output_cfg.clear()
        self.output_tla_options.clear()
        self.output_tla_constants.clear()
        self._parse_behavior()
        self._parse_invariants()
        self._parse_properties()
        self._parse_constants()
        self._parse_override()
        self._parse_const_expr()
        self._parse_state_constraint()
        self._parse_action_constraint()
        self._parse_additional_definitions()
        self._parse_alias()

    def write(self):
        """write parsed buf to file"""
        output_cfg_fn = self.output_cfg_fn
        output_tla_fn = self.output_tla_fn
        output_tla_constants_fn = self.output_tla_constants_fn
        with open(output_cfg_fn, 'w') as cfg_f:
            cfg_f.write('{} on {}\n'.format(self.tag, datetime.now()))
            cfg_f.write('\n\n'.join(filter(None, self.output_cfg)))
            cfg_f.write('\n')
        with open(output_tla_fn, 'w') as tla_f:
            module = '---- MODULE {} ----\n'.format(output_tla_fn.replace('.tla', ''))
            tla_f.write(module)
            tla_f.write('EXTENDS {}, TLC\n\n'.format(self.top_module))
            tla_f.write('\n----\n\n'.join(filter(None, self.output_tla_options)))
            tla_f.write('\n{}\n'.format('=' * len(module)))
            tla_f.write('{} on {}\n'.format(self.tag, datetime.now()))
        if output_tla_constants_fn:
            with open(output_tla_constants_fn, 'w') as tla_f:
                module = '---- MODULE {} ----\n'.format(output_tla_constants_fn.replace('.tla', ''))
                tla_f.write(module)
                tla_f.write('EXTENDS {}\n\n'.format(self.extends_string))
                tla_f.write('\n----\n\n'.join(filter(None, self.output_tla_constants)))
                tla_f.write('\n{}\n'.format('=' * len(module)))
                tla_f.write('{} on {}\n'.format(self.tag, datetime.now()))
            self._set_extends_str(output_tla_constants_fn.replace('.tla', ''))


class ReplaceInit:
    """Replace TLA Init state with a specific state from a trace file"""

    def __init__(self, tla_file: str, trace_file: str, replace_state: int=0, python_init: str='') -> None:
        def choose_state(state_num: int, state_dict: dict, state_str: str, is_last_state: bool) -> str:
            if replace_state == state_num or is_last_state:
                return state_str
            return ''

        self.tla_file = tla_file
        self.trace_file = trace_file
        self.chooser_handler = choose_state
        self.init_module = None
        if python_init:
            try:
                sys.path.insert(1, os.path.dirname(python_init))
                self.init_module = __import__(os.path.basename(python_init).replace('.py', ''))
                sys.path.pop(1)
            except ModuleNotFoundError:
                pass
        if hasattr(self.init_module, 'init_replace_init'):
            if debug:
                eprint('Debug: calling "init_replace_init"')
            self.init_module.init_replace_init(self)

    def set_chooser_handler(self, func) -> None:
        self.chooser_handler = func

    def get_replace_state_str(self):
        try:
            from trace_reader import TraceReader
        except ModuleNotFoundError:
            eprint('Warning:', 'failed to import "trace_reader",', '"init state" is disabled')
            return ''
        tr = TraceReader()
        if hasattr(self.init_module, 'init_trace_reader'):
            if debug:
                eprint('Debug: calling "init_trace_reader"')
            self.init_module.init_trace_reader(tr)
        states = list(tr.trace_reader_with_state_str(self.trace_file))
        for i, state in enumerate(states):
            chosen = self.chooser_handler(i + 1, state[0], state[1], i + 1 == len(states))
            if chosen:
                if debug:
                    eprint('Debug: choose init state: {}{}'.format(
                        i + 1, ' (last state)' if i + 1 == len(states) else ''))
                return chosen
        if debug:
            eprint('Debug: no init state is chosen')
        return ''

    def get_replaced_tla_file_lines(self, replace_str=None) -> list:
        lines = []
        if replace_str is None:
            replace_str = self.get_replace_state_str()
        with open(self.tla_file) as f:
            started = False
            for line in f:
                if not started:
                    if line.startswith('Init ==') and replace_str:
                        started = True
                        lines.append('Init ==\n')
                        lines.append(replace_str)
                        lines.append('\n\n')
                    else:
                        lines.append(line)
                elif line[0] == '\n':
                    started = False
        return lines

    def write(self) -> None:
        replace_str = self.get_replace_state_str()
        if not replace_str:
            return
        tla_lines = self.get_replaced_tla_file_lines(replace_str)
        os.rename(self.tla_file, self.tla_file + '.bak')
        with open(self.tla_file, 'w') as f:
            f.writelines(tla_lines)
        if debug:
            eprint('Debug: replaced Init TLA+ file:', self.tla_file)


class TLCWrapper:
    """TLC cmdline options"""
    _script_dir = os.path.dirname(os.path.realpath(__file__))
    tla2tools_jar = os.path.join(_script_dir, 'tla2tools.jar')
    community_jar = os.path.join(_script_dir, 'CommunityModules-deps.jar')
    tla2tools_url = 'https://github.com/tlaplus/tlaplus/releases/download/{}/tla2tools.jar'
    tla2tool2_jar_latest_version = 'v1.8.0'
    tla2tool2_jar_stable_version = 'v1.7.2' # v1.7.3 becomes slower in some conditions
    community_url = 'https://github.com/tlaplus/CommunityModules/releases/download/{}/CommunityModules-deps.jar'
    community_jar_version = '202103291751' # for v1.7.2 tlc, some classses are not defined (KSubsetValue) in higher versions
    tla2tools_tlc = 'tlc2.TLC'
    tla2tools_server = 'tlc2.tool.distributed.TLCServer'
    tla2tools_worker = 'tlc2.tool.distributed.TLCWorker'
    tla2tools_fpset = 'tlc2.tool.distributed.fp.DistributedFPSet'
    tla2tools_worker_and_fpset = 'tlc2.tool.distributed.fp.TLCWorkerAndFPSet'

    default_config_file = 'config.ini'  # default input file

    # default output files
    default_mc_cfg = 'MC.cfg'
    default_mc_tla = 'MC.tla'
    default_mc_tla_constants = 'MC_constants.tla'
    default_mc_log = 'MC.out'
    default_mc_user = 'MC_user.txt'
    default_mc_states = 'MC_states'
    default_mc_coverage = 'MC_coverage.txt'
    default_mc_ini = 'MC.ini'
    default_mc_trace = 'MC_trace'
    default_tlcwrapper_log = 'tlcwrapper.log'

    task_id_number = 0

    # third-party scripts to run distributed mode
    spssh_dir = os.path.join(_script_dir, 'spssh')
    spssh_sh = os.path.join(spssh_dir, 'spssh.sh')
    spssh_cp_sh = os.path.join(spssh_dir, 'spssh_cp.sh')

    def __init__(self, config_file=None, log_file=True, gen_cfg_fn=None, gen_tla_fn=None, gen_tla_constants_fn=None,
                 summary=None, is_task_id=True, is_split_user_file=True, classpath='', need_community_modules=False,
                 log_output=False):
        """create model dir, chdir, copy files and generate tlc configfile"""
        
        # save current dir
        self.orig_cwd = os.getcwd()

        # default is not simulation mode
        self.simulation_mode = False

        self.distributed_mode = False

        # open config file
        config_file = config_file if config_file is not None else self.default_config_file
        if not hasattr(config_file, 'read'):
            config_file = open(config_file, 'r')
        config_str = config_file.read()
        config_file.close()
        self.cfg = ConfigParser()
        self.cfg.optionxform = str  # case sensitive
        self.cfg.read_string(config_str)

        if 'options' not in self.cfg:
            xprint('Error: config file has no "options" section, run "python3 {} -h" for help'.format(sys.argv[0]))
            raise ValueError('config file has no "options" section')

        # check dependencies and set classpath
        if not need_community_modules and 'community modules' in self.cfg['options']:
            need_community_modules = self.cfg.getboolean('options', 'community modules', fallback=False)
        if not classpath:
            classpath = self.tla2tools_jar
        else:
            classpath = ':'.join([os.path.realpath(i) for i in classpath.split(':')])
            classpath = '{}:{}'.format(classpath, self.tla2tools_jar)
        self.need_community_modules = need_community_modules
        if need_community_modules:
            classpath = '{}:{}'.format(classpath, self.community_jar)
        self._tlc_cmd = ['java', '-XX:+UseParallelGC', '-cp', classpath]
        self.classpath = classpath

        # open log file
        if isinstance(log_file, str):  # if log_file specified, open it before change cwd
            self.log_file = open(log_file, 'w')

        # take model dir
        target = self.cfg.get('options', 'target')

        TLCWrapper.task_id_number += 1
        task_id = '' if not is_task_id else '_{}'.format(TLCWrapper.task_id_number)
        model_name = self.cfg.get('options', 'model name') + datetime.now().strftime("_%Y-%m-%d_%H-%M-%S") + task_id
        os.chdir(os.path.dirname(os.path.realpath(target)))
        os.makedirs(model_name, exist_ok=True)
        for file in os.listdir('.'):
            if file.endswith('.tla'):
                copy2(file, model_name)
        model_dir = os.path.realpath(model_name)
        os.chdir(self.orig_cwd)
        need_separate_constants = self._parse_init_state(os.path.join(model_dir, os.path.basename(target)))
        os.chdir(model_dir)

        # gitignore all generated files
        with open('.gitignore', 'w') as gitignore_f:
            gitignore_f.write('# Generated by tlcwrapper.py\n')
            gitignore_f.write('*\n')

        # set log_output file
        if log_output:
            global wrapper_out_file
            wrapper_out_file = open(self.default_tlcwrapper_log, 'w')

        # check and open log file again
        if log_file:
            if not isinstance(log_file, str):
                self.log_file = open(self.default_mc_log, 'w')
        else:
            self.log_file = None

        # generate config files
        self.gen_cfg_fn = gen_cfg_fn if gen_cfg_fn is not None else self.default_mc_cfg
        self.gen_tla_fn = gen_tla_fn if gen_tla_fn is not None else self.default_mc_tla
        if need_separate_constants and not gen_tla_constants_fn:
            gen_tla_constants_fn = True
        if not gen_tla_constants_fn:
            self.gen_tla_constants_fn = None
        else:
            if gen_tla_constants_fn == True:
                self.gen_tla_constants_fn = self.default_mc_tla_constants
            else:
                self.gen_tla_constants_fn = gen_tla_constants_fn

        TLCConfigFile(self.cfg, self.gen_cfg_fn, self.gen_tla_fn,
            self.gen_tla_constants_fn, target_tla_file=os.path.basename(target)).write()

        # set Java and TLC options
        self.options = []
        # distributed mode slave cmds
        self.cmd_workers = []
        self.cmd_fpsets = []
        self.cmd_workers_fpsets = []
        self.is_split_user_file = is_split_user_file
        self._parse_options()

        with open(self.default_mc_ini, 'w') as f:
            f.write('; {}\n; {}\n\n'.format(*self.get_cmd_str().splitlines()))
            f.write(config_str)

        # init result and summary table
        self.result = None
        self.log_lines = None
        self.init_result()
        self.summary = summary if summary is not None else Summary()


    def __del__(self):
        if hasattr(self, 'log_file') and hasattr(self.log_file, 'close'):
            self.log_file.close()
        global wrapper_out_file
        if hasattr(wrapper_out_file, 'close'):
            wrapper_out_file.close()
            wrapper_out_file = None
        os.chdir(self.orig_cwd)

    def _parse_init_state(self, tla_file):
        if 'init state' in self.cfg:
            opt = self.cfg['init state']
        else:
            return False
        trace_file = opt.get('trace file')
        if not trace_file:
            return False
        replace_state = opt.getint('state', fallback=0)
        python_init = opt.get('python init file')
        ReplaceInit(tla_file, trace_file, replace_state, python_init).write()
        return True

    def _parse_options(self):
        """parse options section"""
        self.options = [self.gen_tla_fn, '-config', self.gen_cfg_fn]
        opt = self.cfg['options']

        def _parse_workers(opt_name, opt_list, class_name):
            client_opt = opt.get(opt_name)
            if not client_opt:
                return
            clients = client_opt.splitlines()
            for c in clients:
                args = self._tlc_cmd.copy()
                args[-1] = ':'.join([os.path.basename(i) for i in args[-1].split(':')])
                args[-1] = os.path.basename(self.tla2tools_jar)
                if self.need_community_modules:
                    args[-1] += ':' + os.path.basename(self.community_jar)
                args.append(class_name)
                args.append(server_name)
                c_opts = c.strip().split()
                _, c_name = c_opts[0].split('@')
                args.insert(1, '-Djava.rmi.server.hostname=' + c_name)
                mem = 0
                if len(c_opts) >= 2:
                    mem = float(c_opts[1])
                    if mem >= 1:
                        mem = int(mem)
                    direct_mem_arg = '-XX:MaxDirectMemorySize=${DIRECT_MEM}m'
                    xmx_mem_arg = '-Xmx${XMX_MEM}m'
                    args.insert(1, xmx_mem_arg)
                    args.insert(1, direct_mem_arg)
                    args.insert(1, '-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet')
                    if len(c_opts) >= 3:
                        args.insert(1, '-Dtlc2.tool.distributed.TLCWorker.threadCount=' + c_opts[2])
                opt_list.append((c_opts[0], mem, args))

        if opt.get('distributed mode') and opt.get('distributed mode').lower() != 'false':
            server_name = opt.get('distributed mode')
            self.distributed_mode = True
            _parse_workers('distributed TLC workers', self.cmd_workers, self.tla2tools_worker)
            _parse_workers('distributed fingerprint server', self.cmd_fpsets, self.tla2tools_fpset)
            _parse_workers('distributed TLC and fingerprint', self.cmd_workers_fpsets, self.tla2tools_worker_and_fpset)
            self._tlc_cmd.insert(1, '-Dtlc2.tool.distributed.TLCServer.expectedFPSetCount={}'.format(
                len(self.cmd_fpsets) + len(self.cmd_workers_fpsets)))
            self.is_split_user_file = False
            self._tlc_cmd.append(self.tla2tools_server)
            if server_name.lower() != 'true':
                self._tlc_cmd.insert(1, '-Djava.rmi.server.hostname=' + server_name)
        else:
            self._tlc_cmd.append(self.tla2tools_tlc)
        
        if self.is_split_user_file:
            self.options += ['-userFile', self.default_mc_user]
        
        if opt.get('stop after'):
            self._tlc_cmd.insert(1, '-Dtlc2.TLC.stopAfter=' + opt.get('stop after'))

        mem = None
        mem_ratio = opt.getfloat('memory ratio')
        if mem_ratio:
            try:
                from psutil import virtual_memory
                mem = int(virtual_memory().total / 1024 / 1024 * mem_ratio)
            except ImportError:
                mem = None
                eprint('Warning:', 'failed to import "psutil",', '"memory ratio" is disabled')
        if mem is None:
            mem = opt.getint('system memory')
        if mem:
            direct_mem = '-XX:MaxDirectMemorySize=' + str(mem // 3 * 2) + 'm'
            xmx = '-Xmx' + str(mem // 3) + 'm'
            self._tlc_cmd.insert(1, xmx)
            self._tlc_cmd.insert(1, direct_mem)
            self._tlc_cmd.insert(1, '-Dtlc2.tool.fp.FPSet.impl=tlc2.tool.fp.OffHeapDiskFPSet')

        dump_states = opt.get('dump states')
        if dump_states:
            if dump_states.startswith('dot'):
                self.options += ['-dump', dump_states, self.default_mc_states]
            elif dump_states.lower() != 'false':
                self.options += ['-dump', self.default_mc_states]

        options_list = [opt.get('workers'), opt.getint('checkpoint minute'), opt.getint('dfs depth'),
                        not opt.getboolean('check deadlock'), opt.getint('coverage minute'),
                        opt.getint('simulation depth'), opt.getint('simulation seed'), opt.get('recover'),
                        opt.getboolean('gzip'), opt.getboolean('generate spec TE'), opt.getboolean('clean up'),
                        opt.get('liveness check'), opt.getboolean('diff trace')]
        options = ['-workers', '-checkpoint', '-dfid', '-deadlock', '-coverage', '-depth', '-seed', '-recover',
                   '-gzip', '-generateSpecTE', '-cleanup', '-lncheck', '-difftrace']
        for i, j in zip(options, options_list):
            if j:
                self.options.append(i)
                if not isinstance(j, bool):
                    self.options.append(str(j))

        simulation_options = []
        simulation_traces_num = opt.getint('simulation traces')
        if simulation_traces_num:
            simulation_options.append('num=' + str(simulation_traces_num))
        simulation_dump_traces = opt.getboolean('simulation dump traces')
        if simulation_dump_traces:
            simulation_options.append('file=' + os.path.join(os.path.realpath('.'), 'trace'))
        simulation_options_str = ','.join(simulation_options)

        if '-depth' in self.options or '-aril' in self.options or simulation_options_str:
            self.options.append('-simulate')
            if simulation_options_str:
                self.options.append(simulation_options_str)
            self.simulation_mode = True
        
        if opt.getboolean('dump trace'):
            self.options += ['-dumpTrace', 'tla', self.default_mc_trace + '.tla',
                             '-dumpTrace', 'json', self.default_mc_trace + '.json']

        if opt.get('other TLC options') is not None:
            for field in opt.get('other TLC options').split('\n'):
                if len(field) != 0:
                    self.options.append(field)
        
        if opt.get('other Java options') is not None:
            for field in reversed(opt.get('other Java options').split('\n')):
                if len(field) != 0:
                    self._tlc_cmd.insert(1, field)

    def get_cmd_str(self):
        """get tlc command line"""
        result = 'cd {}\n{}'.format(os.getcwd(), ' '.join(i for i in chain(self._tlc_cmd, self.options)))
        if self.distributed_mode:
            result += '\n' + '\n'.join(self.get_distributed_workers_cmd()[0])
        return result

    def get_cmd_options(self):
        """get tlc command line list"""
        return os.getcwd(), self._tlc_cmd + self.options

    def get_distributed_workers_cmd(self):
        """get a list a cmd that workers run"""
        cmds = []
        index = 0
        mem_options = []
        client_run_cmds = []
        clients = []
        for i in self.cmd_workers, self.cmd_fpsets, self.cmd_workers_fpsets:
            for j in i:
                index += 1
                cmds.append("# cat <<'EOF' | ssh {} 'export SSH_NO={}; exec bash'".format(j[0], index))
                mem_options.append(j[1])
                client_run_cmds.append(' '.join(j[-1]))
                clients.append(j[0])
        cmds.append('MEM_OPTIONS=(_ {})'.format(' '.join(str(i) for i in mem_options)))
        cmds.append('MY_MEM=${MEM_OPTIONS[$SSH_NO]}')
        cmds.append('''function set_memory() {
    if [ "$MY_MEM" != 0 ]; then
        if [[ "$MY_MEM" =~ 0\\. ]]; then
            MEM_TOTAL=$(($(sed -En '/MemTotal/s/.*[ ]+([0-9]+).*/\\1/p' </proc/meminfo)/1024))
            MY_MEM=$(awk "BEGIN {printf \\"%.0f\\",$MY_MEM*$MEM_TOTAL}")
        fi
        DIRECT_MEM=$((MY_MEM/3*2))
        XMX_MEM=$((MY_MEM/3))
    fi
}''')
        cmds.append("set_memory")
        cmds.append('CMDS=(_\n {})'.format('\n '.join(['"{}"'.format(i) for i in client_run_cmds])))
        cmds.append("set -x; eval '${CMDS[$SSH_NO]}'")
        cmds.append('EOF')
        return cmds, clients

    def raw_run(self):
        """directly call tlc program without analysing the output"""
        self.download_dependencies()
        options = self._tlc_cmd + self.options
        if debug:
            eprint('Debug: cwd:', os.getcwd())
            eprint('Debug: cmd:', options)
        if self.distributed_mode:
            self.run_distributed_workers()
        subprocess.call(options)

    def init_result(self):
        result_key = ['start time', 'finish time', 'time consuming',
                      'diameter', 'total states', 'distinct states', 'queued states',
                      'info', 'errors', 'tlc bug', 'warnings', 'error trace', 'other msg',
                      'coverage', 'exit state']
        result_key_is_list = ['info', 'errors', 'tlc bug', 'warnings', 'error trace', 'other msg', 'coverage']
        self.result = OrderedDict(zip_longest(result_key, tuple()))  # fill None
        for key in result_key_is_list:
            self.result[key] = []
        self.log_lines = []

    @staticmethod
    def download_jar(target, url, default_version, lastest_version_link, overwrite=False):
        def version_numbers(s):
            return [int(i.replace('v', '')) for i in s.split('.')]

        if not os.path.isfile(target) or overwrite:
            try:
                import requests
                version = default_version
                if lastest_version_link:
                    r = requests.get(lastest_version_link)
                    request_version = r.json()['tag_name']
                    if version_numbers(request_version) > version_numbers(default_version):
                        version = request_version
                if debug:
                    eprint('Debug: downloading:', url.format(version))
                r = requests.get(url.format(version), allow_redirects=True)
                with open(target, 'wb') as f:
                    f.write(r.content)
            except Exception as e:
                xprint('Error:', 'failed to download "{}", you should download it manually'.format(
                    os.path.basename(target)))
                raise e

    @classmethod
    def download_tla2tools(cls, latest=False, overwrite=False):
        lastest_version_link = None if not latest else 'https://api.github.com/repos/tlaplus/tlaplus/releases/latest'
        tla2tool2_version = cls.tla2tool2_jar_stable_version if not latest else cls.tla2tool2_jar_latest_version
        cls.download_jar(cls.tla2tools_jar, cls.tla2tools_url, tla2tool2_version, lastest_version_link, overwrite)

    @classmethod
    def download_community_modules(cls, latest=False, overwrite=False):
        lastest_version_link = None if not latest else 'https://api.github.com/repos/tlaplus/CommunityModules/releases/latest'
        cls.download_jar(cls.community_jar, cls.community_url, cls.community_jar_version,
                         lastest_version_link, overwrite)

    def download_dependencies(self):
        self.download_tla2tools()
        if self.need_community_modules:
            self.download_community_modules()
    
    def run_distributed_workers(self):
        if not self.distributed_mode:
            return
        xprint('-' * 16)
        if all(os.path.isfile(i) for i in [self.spssh_sh, self.spssh_cp_sh]):
            cmds, clients = self.get_distributed_workers_cmd()
            client_cmd_str = '\n'.join([ i for i in cmds if not i.startswith('#') ])
            host_cmd_str = "tmux split-window -d -t 0 'exec tail -f -n +1 {}'; exec tail -f -n +1 {}".format(
                self.default_mc_log, self.default_tlcwrapper_log)
            jar_dir = os.path.dirname(self.classpath.split(':')[0])
            run_spssh_cmd = \
                """cat <<'EOF' | {} -f '-maxdepth 1 -name \\*.jar' {} 2>/dev/null | {} -H -S -b -t -s -e -r "{}" {} 2>&1\n""" \
                .format(self.spssh_cp_sh, jar_dir, self.spssh_sh, host_cmd_str, ' '.join(clients))
            run_spssh_cmd += "cd {}\n".format(os.path.basename(jar_dir))
            run_spssh_cmd += client_cmd_str + '\n'
            if debug:
                eprint('Debug:', 'popen cmd:\n{}'.format(run_spssh_cmd))
            output = os.popen(run_spssh_cmd).read()
            if output and debug:
                eprint('Debug:', 'popen cmd output:\n{}'.format(output))
            xprint('Run "tmux attach-session -t {}" to check workers progress'.format(
                re.sub(r'.*\n.*SESSION=(.*)\n', r'\1', output)))
        else:
            xprint('Run below commands on clients:')
            for i, _ in self.get_distributed_workers_cmd():
                xprint(i)
        xprint('-' * 16)

    def run(self):
        """call tlc and analyse output"""
        self.init_result()  # clear result

        title_printed = False
        title_list = ['Current Time', 'Duration', 'Diameter', 'States Found', 'Distinct States', 'Queue Size']
        if self.simulation_mode:
            title_list = [i if i != 'Diameter' else 'Traces' for i in title_list]
        self.summary.init_title(is_simulation=self.simulation_mode)

        def print_state(time):
            nonlocal title_printed
            if type(time) is timedelta:
                m, s = divmod(time.total_seconds(), 60)
                h, m = divmod(m, 60)
                time = '{:d}:{:02d}:{:02d}'.format(int(h), int(m), int(s))
            value_list = [datetime.now().strftime("%H:%M:%S"), str(time), self.result['diameter'],
                          self.result['total states'], self.result['distinct states'], self.result['queued states']]
            if all(i is not None for i in value_list):
                if not title_printed:
                    title_printed = True
                    xprint(('{:<15} ' * len(title_list)).format(*title_list))
                xprint(('{:<15} ' * len(value_list)).format(*value_list))
                for k, v in zip(title_list, value_list):
                    self.summary.add_info(k, v)

        progress_pat = re.compile(r'Progress\(%?(-?[\d,]+)%?\) at (.*): ([\d,]+) s.*, (-?[\d,]+) d.*, (-?[\d,]+) s')
        # finish_pat = re.compile(r'(\d+) states generated, (\d+) distinct states found, (\d+) states left on queue')

        tmp_lines = []
        message_code = -1  # see https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/output/EC.java
        message_type = -1  # see https://github.com/tlaplus/tlaplus/blob/master/tlatools/org.lamport.tlatools/src/tlc2/output/MP.java
        message_type_key = ('info', 'errors', 'tlc bug', 'warnings', 'error trace', 'other msg')
        finish_flag = False
        interrupt_flag = False

        def int_handler(sig, frame):
            nonlocal interrupt_flag
            interrupt_flag = True
        
        signal.signal(signal.SIGINT, int_handler)

        def process_message():
            if len(tmp_lines) == 0:
                return
            line = '\n'.join(tmp_lines)
            self.result[message_type_key[message_type]].append((datetime.now(), line))
            # if message_type_key[message_type] in {'errors', 'warnings'}:
            #     xprint('Error:' if message_type_key[message_type] == 'errors' else 'Warning:', line)
            if message_code == 2185:  # Starting...
                self.result['start time'] = datetime.strptime(line, 'Starting... (%Y-%m-%d %H:%M:%S)')
            elif message_code == 2186:  # Finished in...
                self.result['finish time'] = datetime.strptime(line.split('at')[1], ' (%Y-%m-%d %H:%M:%S)')
                self.result['time consuming'] = self.result['finish time'] - self.result['start time']
                nonlocal finish_flag
                finish_flag = True
                # print_state(self.result['time consuming'])
            elif message_code in {2200, 2206, 2209}:  # Progress...
                progress_match = progress_pat.match(line)
                if not progress_match:
                    if debug:
                        eprint('Debug:', 'Please report this bug: match failed: "{}".'.format(line))
                else:
                    groups = progress_match.groups()
                    self.result['diameter'] = int(groups[0].replace(',', ''))
                    self.result['total states'] = int(groups[2].replace(',', ''))
                    self.result['distinct states'] = int(groups[3].replace(',', ''))
                    self.result['queued states'] = int(groups[4].replace(',', ''))
                    current_time = datetime.strptime(groups[1], '%Y-%m-%d %H:%M:%S')
                    self.result['time consuming'] = current_time - self.result['start time']
                    print_state(self.result['time consuming'])
            elif message_code == 2190:  # Finished computing initial states ...
                states = int(line.split(':')[1].split(' ')[1])
                self.result['diameter'] = 0
                self.result['total states'] = states
                self.result['distinct states'] = states
                self.result['queued states'] = states
                print_state(str(datetime.now() - self.result['start time']).split('.')[0])
            # elif message_code == 2199:  # ... states generated, ... distinct states found, 0 states left on queue.
            #     groups = finish_pat.match(line).groups()
            #     self.result['total states'] = int(groups[0])
            #     self.result['distinct states'] = int(groups[1])
            #     self.result['queued states'] = int(groups[2])
            elif message_code == 2194:  # The depth of the complete state graph search is ...
                diameter = int(line.split(' ')[9].rstrip('.'))
                self.result['diameter'] = diameter
            elif message_code == 2201:  # The coverage statistics
                self.result['coverage'] = [line]
            elif message_code == 2221:  # coverage msg detail
                self.result['coverage'].append(line)
            elif message_code == 2202:  # End of statistics
                self.save_coverage()

        options = self._tlc_cmd + self.options + ['-tool']  # tool mode
        if debug:
            eprint('Debug: cwd:', os.getcwd())
            eprint('Debug: cmd:', options)
        self.download_dependencies()

        with open(self.default_mc_ini, 'a') as f:
            cur_time = datetime.now()
            f.write('\n; CMD: {}\n; START TIME: {}\n'.format(options, cur_time))
            self.summary.add_info('Start Time', cur_time)
            process = subprocess.Popen(options, stdout=subprocess.PIPE, universal_newlines=True)
            if debug:
                eprint('Debug:', 'JAVA PID: {}'.format(process.pid))
            cur_time = datetime.now()
            self.summary.add_info('End Time', cur_time)
            # f.write('; END TIME: {}\n'.format(cur_time))

        self.run_distributed_workers()

        for msg_line in iter(process.stdout.readline, ''):
            if msg_line == '':  # sentinel
                process_message()
                break
            self.log_lines.append(msg_line)
            if self.log_file:
                self.log_file.write(msg_line)
                self.log_file.flush()
            msg_line = msg_line.rstrip()
            if message_code == -1 and msg_line.startswith('@!@!@STARTMSG'):
                process_message()
                message_code, message_type = tuple(int(i) for i in msg_line.split(' ')[1].split(':'))
            elif message_code != -1 and msg_line.startswith('@!@!@ENDMSG ' + str(message_code)):
                process_message()
                message_code, message_type = -1, -1
                tmp_lines = []
            else:
                tmp_lines.append(msg_line)
            if (finish_flag == True and self.distributed_mode == True) or interrupt_flag:
                process.terminate()

        exit_state = process.poll()
        self.result['exit state'] = 0 if exit_state is None else exit_state
        self.summary.add_info('Exit Status', self.result['exit state'])
        self.summary.add_info('Warnings', len(self.result['warnings']))
        self.summary.add_info('Errors', len(self.result['errors']))
        if len(self.result['error trace']):
            self.summary.add_info('Error Trace Depth', len(self.result['error trace']), force=True)
        with open(self.default_mc_ini, 'a') as f:
            cur_time = datetime.now()
            self.summary.add_info('End Time', cur_time)
            self.summary.add_info('Duration', self.summary.current['End Time'] - self.summary.current['Start Time'])
            f.write('; END TIME: {}\n'.format(cur_time))
        return self.result

    def get_log(self):
        return self.log_lines

    def get_summary(self):
        return self.summary

    def save_log(self, filename=None):
        """save tlc output to file"""
        if filename is None:
            filename = self.default_mc_log
        with open(filename, 'w') as f:
            f.writelines(self.log_lines)

    def save_coverage(self, filename=None):
        """save coverage msg to file if it has coverage msgs"""
        if filename is None:
            filename = self.default_mc_coverage
        if len(self.result['coverage']) != 0:
            with open(filename, 'w') as f:
                f.write('\n'.join(self.result['coverage']))
                f.write('\n')

    def print_result(self):
        for _, msg in self.result['warnings']:
            xprint('Warning: ' + msg)
        for _, msg in self.result['errors']:
            xprint('Error: ' + msg)
        for _, msg in self.result['error trace']:
            xprint(msg)
        xprint('Status: errors: {}, warnings: {}, exit_state: {}'.format(
            len(self.result['errors']), len(self.result['warnings']), self.result['exit state']))


def main(config_file, summary_file=None, separate_constants=None, classpath='', need_community_modules=False,
         log_output=False):
    summary = Summary()
    options = tuple()
    for options, config_stringio in BatchConfig(config_file, summary).get():
        xprint('\n{}'.format('#' * 16))
        tlc = TLCWrapper(config_stringio, summary=summary, gen_tla_constants_fn=separate_constants,
            classpath=classpath, need_community_modules=need_community_modules, log_output=log_output)
        if options:
            xprint('Options:')
            for i in options:
                xprint(' ', i.replace('\n', '\n  '))
            xprint('-' * 16)
        tlc.run()
        xprint('-' * 16)
        tlc.print_result()
        summary.finish_current()
        del tlc
    xprint('=' * 16)
    xprint(summary)
    if summary_file or (summary_file is None and options):
        if isinstance(summary_file, str):
            name = summary_file
        else:
            config_file_name = config_file if not hasattr(config_file, 'read') else 'stdin'
            name = "MC_summary_{}_{}.csv".format(
                os.path.basename(config_file_name).replace('.ini', ''), datetime.now().strftime("%Y-%m-%d_%H-%M-%S"))
        summary.print_to_file(name)


def raw_run(config_file, is_print_cmd=False, separate_constants=None, classpath='', need_community_modules=False):
    for _, config_stringio in BatchConfig(config_file).get():
        tlc = TLCWrapper(config_stringio, log_file=None, is_split_user_file=False,
            gen_tla_constants_fn=separate_constants, classpath=classpath, need_community_modules=need_community_modules)
        if is_print_cmd:
            xprint(tlc.get_cmd_str())
        else:
            tlc.raw_run()
        del tlc


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Run TLC in CMD")

    parser.add_argument('-j', dest='classpath', action='store', required=False,
                        help='Java classpath to use')
    parser.add_argument('-g', dest='get_cmd', action='store_true', required=False,
                        help="Generate TLC config files and print Java CMD strings")
    parser.add_argument('-r', dest='raw_run', action='store_true', required=False,
                        help="Run without processing TLC output")
    parser.add_argument('-s', dest='no_summary', action='store_true', required=False,
                        help="Do not save summary file", default=False)
    parser.add_argument('-d', dest='download_jar', action='store_true', required=False,
                        help="Download tla2tools.jar and CommunityModules-deps.jar and exit", default=False)
    parser.add_argument('-D', dest='stable_version', action='store_true', required=False, default=False,
                        help="Delete existing jars and download with stable version instead of latest version")
    parser.add_argument('-c', dest='separate_constants', action='store_true', required=False,
                        help="Separate constants and model options into two files", default=False)
    parser.add_argument(dest='config_ini', metavar='config.ini', action='store', nargs='?',
                        help='Configuration file (if not presented, stdin is used)')
    parser.add_argument('-m', dest='community_modules', action='store_true', required=False,
                        help='Require community modules')
    parser.add_argument('-n', dest='no_debug', action='store_true', required=False,
                        help='Not to print debug messages')

    args = parser.parse_args()

    if args.download_jar or args.stable_version:
        if args.stable_version:
            eprint('Info: please note that the stable TLC version has limited support for CommunityModules')
        is_latest = not args.stable_version
        TLCWrapper.download_tla2tools(latest=is_latest, overwrite=args.stable_version)
        TLCWrapper.download_community_modules(latest=is_latest, overwrite=args.stable_version)
        exit(0)
    if args.no_debug:
        debug = False
    if not args.config_ini:
        args.config_ini = sys.stdin
    if args.get_cmd:
        raw_run(args.config_ini, is_print_cmd=True, separate_constants=args.separate_constants,
            classpath=args.classpath, need_community_modules=args.community_modules)
    elif args.raw_run:
        raw_run(args.config_ini, is_print_cmd=False, separate_constants=args.separate_constants,
            classpath=args.classpath, need_community_modules=args.community_modules)
    else:
        main(args.config_ini, not args.no_summary, separate_constants=args.separate_constants,
            classpath=args.classpath, need_community_modules=args.community_modules, log_output=True)

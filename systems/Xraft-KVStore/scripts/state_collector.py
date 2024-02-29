#!/usr/bin/python3

import re
from functools import partial

convert_hex = partial(int, base=16)

role_change_pat = re.compile(r".*node .*, role state changed -> ([a-zA-Z]+)NodeRole\{term=([0-9]+)")
role_change_groups = (("state", str), ("current_term", int))

become_follower_pat = re.compile(r'.*current (leader) is .*, term ([0-9]+)')
become_follower_groups = (("state", lambda x: "Follower"), ("current_term", int),)

become_leader_pat = re.compile(r'.*become (leader), term ([0-9]+)')
become_leader_groups = (("state", lambda x: "Leader"), ("current_term", int),)

advance_commit_idx_pat = re.compile(r'.*advance commit index from [0-9]+ to ([0-9]+)')
advance_commit_idx_groups = (("commit_idx", int),)

pat_dict =\
    (
        (role_change_pat, role_change_groups),
        (become_follower_pat, become_follower_groups),
        (become_leader_pat, become_leader_groups),
        (advance_commit_idx_pat, advance_commit_idx_groups)
    )

while True:
    try:
        line = input()
    except:
        break
    for i, v in enumerate(pat_dict):
        pat, groups = v
        m = pat.match(line)
        if not m:
            continue
        for a, b in zip(groups, m.groups()):
            name, conv = a
            print("{}={}".format(name, conv(b)), flush=True)

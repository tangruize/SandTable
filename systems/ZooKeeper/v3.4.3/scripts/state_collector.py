#!/usr/bin/python3

import re
from functools import partial

send_not_pat = re.compile(r'.*\[myid:[0-9]+\] - DEBUG \[QuorumPeer[^ ]+ - Sending Notification: ([0-9]+) \(n.leader\), (0x[0-9A-Za-z]+) \(n.zxid\), (0x[0-9A-Za-z]+) \(n.round\), [0-9]+ \(recipient\), [0-9]+ \(myid\), (0x[0-9A-Za-z]+) \(n.peerEpoch\)')

convert_hex = partial(int, base=16)

send_not_groups = (("proposedLeader", int), ("proposedZxid", convert_hex), ("logicalclock", convert_hex), ("proposedEpoch", convert_hex),)

pat_dict = ((send_not_pat, send_not_groups),)

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

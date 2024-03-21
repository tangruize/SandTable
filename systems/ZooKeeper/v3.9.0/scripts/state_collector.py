#!/usr/bin/python3

import re
from functools import partial

convert_hex = partial(int, base=16)

# send notification
# FastLeaderElection.java#L705: "Sending Notification: {} (n.leader), 0x{} (n.zxid), 0x{} (n.round), {} (recipient), {} (myid), 0x{} (n.peerEpoch) "
send_not_pat = re.compile(r'.*Sending Notification: ([0-9]+) \(n.leader\), (0x[0-9A-Za-z]+) \(n.zxid\), (0x[0-9A-Za-z]+) \(n.round\), [0-9]+ \(recipient\), [0-9]+ \(myid\), (0x[0-9A-Za-z]+) \(n.peerEpoch\)')
send_not_groups = (("proposedLeader", int), ("proposedZxid", convert_hex), ("logicalclock", convert_hex), ("proposedEpoch", convert_hex),)

# update proposal
# FastLeaderElection.java#L818: "Updating proposal: {} (newleader), 0x{} (newzxid), {} (oldleader), 0x{} (oldzxid)"
update_prop_pat = re.compile(r'.*Updating proposal: ([0-9]+) \(newleader\), (0x[0-9A-Za-z]+) \(newzxid\), [0-9]+ \(oldleader\), 0x[0-9A-Za-z]+ \(oldzxid\)')
update_prop_groups = (("proposedLeader", int), ("proposedZxid", convert_hex))

# LeaderProcessFOLLOWERINFO
# LearnerHandler#L511: "Follower sid: {} : info : {}"
follower_sid_pat = re.compile(r'.*Follower sid: ([0-9]+)')
follower_sid_groups = (("follower_sid", int),)

# FollowerProcessLEADERINFO
# Follower.java#L107: "Peer state changed: {} - {}"
zab_state_pat = re.compile(r'.*Peer state changed: .* - (.*)')
zab_state_groups = (("zabState", str),)

received_newleader_pat = re.compile(r'.*Learner received (.*) message')
received_newleader_groups = (("msg_type", str),)

# LeaderSyncFollower
leader_sync_pat = re.compile(r'.*Sending (.*) zxid=(0x[0-9A-Za-z]+)')
leader_sync_groups = (("sync_msg_type", str), ("zxid", convert_hex))
leader_sync_pat2 = re.compile(r'Sending (.*) last zxid of peer is .*, zxid of leader is (0x[0-9A-Za-z]+)')
leader_sync_groups2 = (("sync_msg_type", lambda x: x.upper()[0:4]), ("zxid", convert_hex))

# LeaderProcessACKLD
leader_ackld_pat = re.compile(r'.*Received (.*) message')
leader_ackld_groups = (("msg_type", str),)

pat_dict = ((send_not_pat, send_not_groups),
            (update_prop_pat, update_prop_groups),
            (follower_sid_pat, follower_sid_groups),
            (zab_state_pat, zab_state_groups),
            (received_newleader_pat, received_newleader_groups),
            (leader_sync_pat, leader_sync_groups),
            (leader_sync_pat2, leader_sync_groups2),
            (leader_ackld_pat, leader_ackld_groups))

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

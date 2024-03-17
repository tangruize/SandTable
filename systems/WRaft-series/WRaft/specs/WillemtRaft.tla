------------------------------- MODULE WillemtRaft -------------------------------
\* This is the formal specification for the Willemt/raft consensus algorithm.
\* See https://github.com/willemt/raft
\*
\* Copyright (c) 2021, Ruize Tang
\* Licensed under the MIT License.

\* NOTE: Modelled: leader election, log replication and log compaction.
\*       Not modelled: Membership change, last applied index, (AE) first index

\* TODO: Network partition is strange and needs to be rewritten. If you want to
\*       use it, set PartitionDisconnected to FALSE (default), and set 
\*       PartitionNodes to 1.
\* TODO: Invariant FollowerLogLELeaderLogAfterAE may have false positives
\*       if the number of servers is greater than 3. It should be improved.
\* TODO: BecomeFollowerHelper's logic is too complex to read. Improve it.

EXTENDS Naturals, FiniteSets, Sequences, TLC

\* The set of server IDs
CONSTANTS Server

\* The set of requests that can go into the log.
CONSTANTS Value

\* Server states
CONSTANTS Follower, Candidate, Leader

\* A reserved value
CONSTANTS Nil

\* Message types
CONSTANTS RequestVoteRequest,   RequestVoteResponse,
          AppendEntriesRequest, AppendEntriesResponse,
          SnapshotRequest

\* Parameters to trim/constrain TLC scheduling.

\*CONSTANTS MaxSentMsgs,          \* Maximum number of messages sent.
\*          MaxRecvMsgs,          \* Maximum number of messages received.
\*          MaxWireMsgs,          \* Maximum number of messages on the wire.
\*          MaxDropMsgFailures,   \* Maximum number of messages dropped.
\*          MaxDupMsgFailures,    \* Maximum number of messages duplicated.
\*          MaxUnorderFailures,   \* Maximum number of messages recved unorderly
\*          MaxTimeoutFailures,   \* Maximum times of timeout (i.e. elections).
\*          MaxRestartFailures,   \* Maximum times of restart.
\*          MaxFailures,          \* Maximum failures in total.
\*          MaxClientOperations,  \* Maximum times of client requests.
\*          MaxHeartbeat,         \* Maximum times of leader heartbeat.
\*          MaxLogs,              \* Maximum log length of each server.
\*          MaxTerm,              \* Maximum current term of each server.
\*          MinContNormalActions, \* Minimal continuous normal actions.
\*          MaxContNormalActions, \* Maximum continuous normal actions.
\*          PartitionNodes,       \* Nodes number for one network partition.
\*          PartitionRecovery,    \* Maximum times of network partition cure.
\*          MinLogCapacity,       \* Minimal initial log capacity.
\*          MaxSnapshot,          \* Maximum times of snapshot
\*          PartitionDisconnected,\* Is partition nodes disconnected TRUE/FASLE
\*          IgnoreInvNumbers      \* Set of inv's number used to ignore errors

\* See above: [ MaxSentMsgs: Nat, MaxRecvMsgs: Nat, ... ]
CONSTANTS Parameters

----
\* Variables

\* Set of messages. Simulates network channel. Message have uniq seq numbers.
\* Type: { [ type: {RequestVoteRequest, ...}, from: Server, to: Server,
\*           seq: Nat, body: [ ... ] ] }
\* Body RequestVoteRequest: 
\*      [ term: Nat, candidate: Server, lastLogIdx: Nat, LastLogTerm: Nat ]
\* Body RequestVoteResponse:
\*      [ term: Nat, voteGranted: {TRUE, FALSE} ]
\* Body AppendEntriesRequest:
\*      [ term: Nat, prevLogIdx: Nat, prevLogTerm: Nat, leaderCommit: Nat,
\*        entries: <<[...]>> ]
\* Body AppendEntriesResponse:
\*      [ term: Nat, success: {TRUE, FALSE}, curIdx: Nat ]
\*      (curIdx helps Leader decrease the corresponding node's nextIdx quickly.)
\* Body SnapshotRequest:
\*      [ term: Nat, lastIdx: Nat, lastTerm: Nat ]
VARIABLES messages

\* Per server variables

\* Persistent state
VARIABLES currentTerm,  \* The server's current term number. Inited to 0, 
                        \* increase monotonically.
          votedFor      \* Who it voted for in current term. Nil if not voted
VARIABLES log           \* Log entries. Head index is 1.
                        \* Type: [ s: << [ term |-> xx, value |-> xx ], .. >> ]
VARIABLES logInfo       \* Base log index since log is compacted

\* Volatile state
VARIABLES state,            \* One of {Follower, Candidate, Leader}
          commitIdx         \* Highest index known to be committed.
                            \* Start from 0, increases monotonically.
\*VARIABLES lastAppliedIdx    \* Highest index applied to state machine. Start
\*                            \* from 1, increases monotonically. (not modelled)

\* Only used by Leader. But each sever contains those variables.
VARIABLES nextIdx   \* Next entry to send. Inited to current log index + 1
VARIABLES matchIdx  \* Highest index known to be replicated. Inited to 0,
                    \* increases monotonically.

\* Only used by Candidate. But each sever contains those variables.
VARIABLES votesGranted      \* Who voted for me.

\* Snapshot metadata
VARIABLES snapshotLastIdx,  \* the last entry in the log the snapshot replaces
          snapshotLastTerm  \* the term of this entry

\* End of per server variables.

\* State constraint recorder.
\* Type: [ nSent: Nat, nRecv: Nat, nWire: Nat, nDrop: Nat, nDup: Nat,
\*         nUnorder: Nat, nTimeout: Nat, nRestart: Nat, nOp: Nat, nLog, Nat,
\*         maxTerm: Nat, nCont: Nat, nCure: Nat, lock: [...], pc: ACTION_NAME,
\*         partNodes: SUBSET Server, nSnapshot: Nat, noInv: {1,2,..} ]
\* nSent/nRecv/nWire: network message count of sent/recv/on-the-wire.
\* nDrop/nDup/nUnorder: network failures count.
\* nTimeout/nRestart: node failures count.
\* nOp: client requests count.
\* nLog/maxTerm: current max log length and max term.
\* nCont: continuous normal actions count.
\* pc: action name and args
\* inv: invariants to evaluate
\* nCure: network partion recovered times
\* partNodes: nodes in the set cannot communicate with nodes not in the set
\* nSnapshot: log compaction count
\* noInv: not to exit TLC even if those inv evaluated as FALSE
\* lock:
\* Loop a broadcast action (e.g. send AppendEntriesRequest).
\*  [ type: { RequestVoteRequest, AppendEntriesRequest, SnapshotRequest},
\*    args: [ from: Server, to: Server ] ]
VARIABLES scr

----
\* Useful vars groups
networkVars     == <<messages>>
serverVars      == <<currentTerm, votedFor, state>>
candidateVars   == <<votesGranted>>
leaderVars      == <<nextIdx, matchIdx>>
logStoreVars    == <<log, logInfo>>
logVars         == <<logStoreVars, commitIdx>>
snapshotVars    == <<snapshotLastIdx, snapshotLastTerm>>
noSnapshotVars  == <<serverVars, candidateVars, leaderVars, logVars>>
noNetworkVars   == <<noSnapshotVars, snapshotVars>>
noLogVars       == <<serverVars, candidateVars, leaderVars, commitIdx,
                     snapshotVars>>
noScrVars       == <<noNetworkVars, networkVars>>

----
\* Helpers

\* Check if servers set (ss) is quorum.
IsQuorum(ss) == Cardinality(ss) * 2 > Cardinality(Server)

\* n*2^t
Exp2t(n, t) ==
    LET F[i \in 0..t] == IF i = 0 THEN n ELSE F[i-1] * 2
    IN F[t]

\* Get log length of server s.
LogLen(s) == logInfo[s].count
\* Get last idx of server s.
LastIdx(s) == LogLen(s) + logInfo[s].base
LastIdxNext(s) == logInfo'[s].base + logInfo'[s].count

\* Check server state.
IsLeader   (s)  == state[s] = Leader
IsFollower (s)  == state[s] = Follower
IsCandidate(s)  == state[s] = Candidate

\* Check if entry ety is null.
IsNullEntry(ety) == ety = Nil

\* Get entries from idx to end.
GetEntriesBaseHelper(entries, idx, base) ==
    IF idx <= base
    THEN Assert(FALSE, <<"GetEntriesBaseHelper: idx <= base", idx, base>>)
    ELSE IF Len(entries) < idx - base
         THEN <<>>
         ELSE SubSeq(entries, idx - base, Len(entries))
GetEntriesHelper(entries, idx) == GetEntriesBaseHelper(entries, idx, 0)
\* Get entry at idx
GetEntryBaseHelper(entries, idx, base) ==
    IF \/ idx = 0
       \/ idx <= base
       \/ Len(entries) < idx - base
       \/ Len(entries) = 0
    THEN Nil
    ELSE entries[idx - base]
GetEntryHelper(entries, idx) == GetEntryBaseHelper(entries, idx, 0)
\* Get entries from idx to end.
GetEntries(s, idx) == GetEntriesBaseHelper(log[s], idx, logInfo[s].base)
\* Get entries from idx to data structure end.
GetEntriesForAppend(s, idx) ==
    LET tmp == GetEntries(s, idx)
        len == Len(tmp)
        i   == (logInfo'[s].front + idx - logInfo'[s].base - 1) % logInfo'[s].size
        cnt == IF LastIdx(s) < idx \/ idx <= logInfo[s].base
               THEN 0
               ELSE IF i < logInfo[s].back
                    THEN logInfo[s].back - i
                    ELSE logInfo[s].size - i
    IN IF cnt > len
       THEN Assert(FALSE, <<"GetEntriesForAppend: cnt > len",
                            tmp, i, cnt, len, logInfo[s]>>)
       ELSE IF len < 1
            THEN <<>>
            ELSE SubSeq(tmp, 1, cnt)
GetEntriesNext(s, idx) == GetEntriesBaseHelper(log'[s], idx, logInfo'[s].base)
\* Get entries from idx to data structure end.
GetEntriesForAppendNext(s, idx) ==
    LET tmp == GetEntriesNext(s, idx)
        len == Len(tmp)
        i   == (logInfo'[s].front + idx - logInfo'[s].base - 1) % logInfo'[s].size
        cnt == IF LastIdxNext(s) < idx \/ idx <= logInfo'[s].base
               THEN 0
               ELSE IF i < logInfo'[s].back
                    THEN logInfo'[s].back - i
                    ELSE logInfo'[s].size - i
    IN IF cnt > len
       THEN Assert(FALSE, <<"GetEntriesForAppend: cnt > len",
                            tmp, i, cnt, len, logInfo[s]>>)
       ELSE IF len < 1
            THEN <<>>
            ELSE SubSeq(tmp, 1, cnt)
\* Get entry at idx
GetEntry(s, idx) == GetEntryBaseHelper(log[s], idx, logInfo[s].base)
\* Get entry at idx
GetEntryNext(s, idx) == GetEntryBaseHelper(log'[s], idx, logInfo'[s].base)
\* Get entries from head to idx.
GetEntriesToIdxBaseHelper(entries, idx, base) ==
    IF idx < base
    THEN <<>>
    ELSE IF Len(entries) < idx - base
         THEN entries
         ELSE SubSeq(entries, 1, idx - base)
GetEntriesToIdxHelper(entries, idx) ==
    GetEntriesToIdxBaseHelper(entries, idx, 0)
GetEntriesToIdx(s, idx) ==
    GetEntriesToIdxBaseHelper(log[s], idx, logInfo[s].base)

\* Check if server s entry[idx] is null.
IsNullEntryIdx(s, idx)  ==
    IF LastIdx(s) < idx \/ logInfo[s].base >= idx THEN TRUE ELSE FALSE
IsNullEntryIdxNext(s, idx)  ==
    IF LastIdxNext(s) < idx \/ logInfo'[s].base >= idx THEN TRUE ELSE FALSE
\* Check if server s entry[idx].term equals term
NotEqualEntryTerm(s, idx, term) ==
    IF IsNullEntryIdx(s, idx)
    THEN TRUE
    ELSE log[s][idx - logInfo[s].base].term /= term

\* fix election bug
\* Get last term of server s.
LastTerm(s) == LET idx == LastIdx(s)
                   ety == GetEntry(s, idx)
               IN IF IsNullEntry(ety)
                  THEN snapshotLastTerm[s]
                  ELSE ety.term

LogUpdate(s, log_tuple) ==
    /\ log'     = [ log     EXCEPT ![s] = log_tuple[1] ]
    /\ logInfo' = [ logInfo EXCEPT ![s] = log_tuple[2] ]

\* Log load from snapshot. Update logInfo and log
LogLoadFromSnapshot(s, lastIdx) ==
    LogUpdate(s, << <<>>, [ count |-> 0, front |-> 0, size |-> logInfo[s].size, 
                            back  |-> 0, base  |-> lastIdx ] >>)

\* Poll starting n entries
LogPollEntriesHelper(s_log, s_info, n) ==
    IF n < 1 \/ n > s_info.count THEN <<s_log, s_info>>
    ELSE LET s_info_tmp == [ count |-> s_info.count - n,
                             front |-> (s_info.front + n) % s_info.size,
                             size  |-> s_info.size, 
                             back  |-> s_info.back,
                             base  |-> s_info.base + n ]
             s_log_tmp  == SubSeq(s_log, n + 1, Len(s_log))
         IN <<s_log_tmp, s_info_tmp>>

LogPollEntries(s, n) ==
    LogUpdate(s, LogPollEntriesHelper(log[s], logInfo[s], n))

\* Append entries to log
LogAppendEntriesHelper(s_log, s_info, entries) ==
    IF Len(entries) < 1 THEN <<s_log, s_info>>
    ELSE LET n == Len(entries)
             enlarge == (s_info.count + n - 1) \div s_info.size
             needEnlarge == enlarge > 0
             size == IF needEnlarge
                     THEN Exp2t(s_info.size, enlarge)
                     ELSE s_info.size
             s_info_tmp == [ count |-> s_info.count + n,
                             front |-> IF needEnlarge THEN 0 ELSE s_info.front,
                             size  |-> size,
                             back  |-> IF needEnlarge
                                       THEN s_info.count + n
                                       ELSE (s_info.back + n) % size,
                             base  |-> s_info.base ]
             s_log_tmp  == s_log \o entries
         IN <<s_log_tmp, s_info_tmp>>

LogAppendEntries(s, entries) ==
    LogUpdate(s, LogAppendEntriesHelper(log[s], logInfo[s], entries))

\* Pop ending n entries
LogPopEntriesHelper(s_log, s_info, n) ==
    IF n < 1 THEN <<s_log, s_info>>
    ELSE IF n > s_info.count THEN Assert(FALSE, "Delete more than count")
         ELSE LET s_info_tmp == [ count |-> s_info.count - n,
                                  front |-> s_info.front,
                                  size  |-> s_info.size,
                                  back  |-> (s_info.back - n) % s_info.size,
                                  base  |-> s_info.base ]
                  s_log_tmp  == SubSeq(s_log, 1, Len(s_log) - n)
              IN <<s_log_tmp, s_info_tmp>>

LogPopEntries(s, n) ==
    LogUpdate(s, LogPopEntriesHelper(log[s], logInfo[s], n))

\* Combine pop and append ops for AppendEntries Request
LogCombineOpsHelper(s_log, s_info, n_pop, entries) ==
    LET pop_tmp    == LogPopEntriesHelper(s_log, s_info, n_pop)
        append_tmp == LogAppendEntriesHelper(pop_tmp[1], pop_tmp[2], entries)
    IN append_tmp

LogCombineOps(s, n_pop, entries) ==
    LogUpdate(s, LogCombineOpsHelper(log[s], logInfo[s], n_pop, entries))

\* Get log-entries that matched entries (delete not matched entries)
GetMatchEntries(s, entries, prevLogIdx) ==
    LET xlog == log[s]
        F[i \in 0..Len(entries)] ==
            IF i = 0
            THEN Nil
            ELSE LET ety2     == GetEntryHelper(entries, i)
                     entries1 == GetEntriesToIdx(s, prevLogIdx + i - 1)
                     entries2 == GetEntriesHelper(entries, i)
                 IN IF /\ F[i-1] = Nil
                       /\ prevLogIdx + i > logInfo[s].base
                       /\ NotEqualEntryTerm(s, prevLogIdx + i, ety2.term)
                    THEN <<entries1, entries2>>
                    ELSE F[i-1]
        log_tuple == F[Len(entries)]
    IN IF log_tuple = Nil
       THEN <<xlog, logInfo[s]>>
       ELSE LogCombineOpsHelper(xlog, logInfo[s],
                                Len(xlog) - Len(log_tuple[1]), log_tuple[2])

\* Return the minimum value from a set, or undefined if the set is empty.
Min(s) == CHOOSE x \in s : \A y \in s : x <= y
\* Return the maximum value from a set, or undefined if the set is empty.
Max(s) == CHOOSE x \in s : \A y \in s : x >= y

GetPartNodes(num) == CHOOSE x \in SUBSET Server: Cardinality(x) = num

GetParameter(p)     == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE 0
GetParameterBool(p) == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE FALSE
GetParameterSet(p)  == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE {}

----
\* Invariants

\* Inv 1: at most one leader per term
AtMostOneLeaderPerTerm ==
    LET TwoLeader == \E i, j \in Server:
                        /\ i /= j
                        /\ currentTerm[i] = currentTerm[j]
                        /\ state[i] = Leader
                        /\ state[j] = Leader
    IN ~TwoLeader

\* Inv 2: committed log should be replicated to majority nodes
CommittedLogReplicatedMajority ==
     \A i \in Server:
        IF state[i] /= Leader \/ commitIdx[i] = 0
        THEN TRUE
        ELSE LET entries == GetEntriesToIdxBaseHelper(log[i], commitIdx[i],
                                                      logInfo[i].base)
                 len     == Len(entries)
                 nServer == Cardinality(Server)
                 F[j \in 0..nServer] ==
                    IF j = 0
                    THEN <<{}, {}>>
                    ELSE LET k == CHOOSE k \in Server: k \notin F[j-1][1]
                             logLenOk == LastIdx(k) >= commitIdx[i]
                             kEntries == GetEntriesToIdxBaseHelper(log[k],
                                            commitIdx[i], logInfo[k].base)
                             minLen == Min({len, Len(kEntries)})
                         IN IF /\ logLenOk
                               /\ \/ minLen = 0
                                  \/ SubSeq(entries, Len(entries) + 1 - minLen,
                                            Len(entries)) = 
                                     SubSeq(kEntries, Len(kEntries)+1 - minLen,
                                            Len(kEntries))
                             THEN <<F[j-1][1] \union {k}, F[j-1][2] \union {k}>>
                             ELSE <<F[j-1][1] \union {k}, F[j-1][2]>>
             IN IsQuorum(F[nServer][2])

\* Inv 3: Committed log should be durable (i.e. cannot be rolled back)
CommittedLogDurable(pc) ==
  ~UNCHANGED <<commitIdx, snapshotLastIdx, commitIdx, log, logInfo>> =>
    IF pc[1] = "Restart" THEN TRUE ELSE
    \A i \in Server:
        LET lenNext == commitIdx'[i] - snapshotLastIdx'[i]
            lenCur  == commitIdx[i] - snapshotLastIdx[i]
            len     == Min({lenNext, lenCur})
            idx     == Min({commitIdx'[i], commitIdx[i]})
            logNext == GetEntriesToIdxBaseHelper(log'[i], idx, logInfo'[i].base)
            logCur  == GetEntriesToIdx(i, idx)
        IN IF len = 0 \/ Len(logNext) = 0 \/ Len(logCur) = 0 THEN TRUE
           ELSE /\ Len(logNext) >= len
                /\ Len(logCur) >= len
                /\ SubSeq(logNext, Len(logNext) + 1 - len, Len(logNext)) =
                   SubSeq(logCur, Len(logCur) + 1 - len, Len(logCur))

CommittedIndexHasSameTerm(pc) ==
  ~UNCHANGED commitIdx =>
    LET curr == pc[1]
        f == pc[2]
        l == pc[3]
    IN
    IF /\ curr = "HandleAppendEntriesRequest: success"
       /\ commitIdx[f] /= commitIdx'[f]
       /\ commitIdx'[f] = snapshotLastIdx'[l]
    THEN LET ety == GetEntryNext(f, commitIdx'[f])
         IN IF ety /= Nil THEN ety.term = snapshotLastTerm'[l] ELSE TRUE
    ELSE TRUE

\* Inv 4: Follower's log is less than or equal to leader's after
\*        receiving append entries and changing its log.
\* TODO: fix bug: Leader may demote and its log may be rolled back.
\*       should compare leader's term with msg's term and then check current
\*       index. However, it won't appear in 3-server scenario
FollowerLogLELeaderLogAfterAE(pc) ==
  ~UNCHANGED log =>
    LET curr     == pc[1]
        follower == pc[2]
        leader   == pc[3]
    IN IF curr \in { "HandleAppendEntriesRequest: log mismatch",
                     "HandleAppendEntriesRequest: success" }
       THEN IF log[follower] /= log'[follower]
            THEN LastIdxNext(follower) <= LastIdxNext(leader)
            ELSE TRUE
       ELSE TRUE

\* Inv 5: Monotonic current term
MonotonicCurrentTerm ==
  ~UNCHANGED currentTerm =>
    \A i \in Server: currentTerm' [i] >= currentTerm[i]

\* Inv 6: Monotonic commit index
MonotonicCommitIdx(pc) ==
  ~UNCHANGED commitIdx =>
    \A i \in Server: IF pc[1] = "Restart"
                     THEN TRUE
                     ELSE commitIdx'[i] >= commitIdx[i]

\* Inv 7: Monotonic match index
MonotonicMatchIdx(pc) ==
  ~UNCHANGED matchIdx =>
    \A i \in Server:
        IF state[i] = Leader
        THEN \A j \in Server:
            \/ matchIdx'[i][j] >= matchIdx[i][j]
            \/ pc[1] = "Restart" /\ matchIdx'[i][j] = 0
        ELSE TRUE

\* Inv 8: (TLA+ internal) logInfo count equals log length
LogInfoCountEqLogLen == \A i \in Server: Len(log[i]) = logInfo[i].count

\* Inv 9: snapshot last index is less than or equal to commit index
SnapshotIdxLECommitIdx ==
    \A i \in Server:
        \/ commitIdx[i] = 0
        \/ snapshotLastIdx[i] <= commitIdx[i]

\* Inv 10: next index is greater than 0
NextIdxGtZero ==
  ~UNCHANGED nextIdx =>
    \A i \in Server:
        IF state[i] = Leader
        THEN \A j \in Server: nextIdx'[i][j] > 0
        ELSE TRUE

\* Inv 11: next index is greater than match index
NextIdxGtMatchIdx ==
    \A i \in Server:
        IF state[i] = Leader
        THEN \A j \in Server: nextIdx[i][j] > matchIdx[i][j]
        ELSE TRUE

\* Inv 12: HandleAppendEntriesResponse retry msg should not be empty
AEResponseNoEmptyRetry(pc) ==
  ~UNCHANGED messages =>
    IF \/ pc[1] /= "HandleAppendEntriesResponse: mismatch and retry"
       \/ Cardinality(messages) /= Cardinality(messages')  \* dropped
    THEN TRUE
    ELSE LET m == CHOOSE m \in messages': m.seq = scr.nSent + 1
         IN IF m.type = AppendEntriesRequest
            THEN Len(m.body.entries) /= 0
            ELSE m.type = SnapshotRequest

\* Invariants helpers. Evaluated in actions so that it is capable of comparing
\* next state with current and makes it easy to evaluate which inv is violated.
\* InvHelper(pc) == <<CommittedLogReplicatedMajority>>
InvHelper(pc) ==
    <<
        CommittedLogDurable(pc),            \* violated
        CommittedIndexHasSameTerm(pc),      \* violated, same effect as above
        FollowerLogLELeaderLogAfterAE(pc),  \* violated
        MonotonicCurrentTerm,               \* violated
        AEResponseNoEmptyRetry(pc),         \* violated
        MonotonicCommitIdx(pc),
        MonotonicMatchIdx(pc),
        NextIdxGtZero
    >>
----

\* Below are scr helpers
ScrGetHelper(member)    == (member :> scr[member])
ScrIncHelper(member)    == (member :> scr[member] + 1)
NetIncBy(member, number) == (member :> scr[member] + number)
ScrIncSent              == LET num1 == Cardinality(messages')
                               num2 == Cardinality(messages)
                           IN IF \/ num1 > num2
                                 \/ num1 = num2 /\ messages' /= messages
                              THEN ScrIncHelper("nSent")
                              ELSE ScrGetHelper("nSent")
ScrIncRecv              == ScrIncHelper("nRecv")
ScrIncDrop              == ScrIncHelper("nDrop")
ScrIncDup               == ScrIncHelper("nDup")
ScrIncUnorder           == ScrIncHelper("nUnorder")
ScrIncTimeout           == ScrIncHelper("nTimeout")
ScrIncRestart           == ScrIncHelper("nRestart")
ScrIncOp                == ScrIncHelper("nOp")
ScrIncAe                == ScrIncHelper("nAe")
ScrIncCont              == ScrIncHelper("nCont")
ScrIncSnapshot          == ScrIncHelper("nSnapshot")
ScrNoIncCont            == ScrGetHelper("nCont")
ScrClearCont            == ("nCont" :> 0)
ScrSetWire              == ("nWire" :> Cardinality(messages'))
ScrSetPc(s)             == ("pc"    :> s)
ScrSetInv(i)            == ("inv"   :> i)
ScrSetLock(l)           == ("lock"  :> l)
ScrUnsetLock            == ("lock"  :> Nil)
ScrIsLocked             == scr.lock /= Nil
ScrNotLocked            == scr.lock  = Nil
ScrGetLockType          == IF ScrIsLocked THEN scr.lock.type ELSE Nil
ScrDeleteLockArg(a)     == IF ScrNotLocked
                           THEN ScrUnsetLock
                           ELSE LET s == scr.lock.args \ {a}
                                IN IF Cardinality(s) = 0
                                   THEN ScrUnsetLock
                                   ELSE ("lock" :> [scr.lock EXCEPT !.args = s]) 
ScrSetLog               == ("nLog" :>
                              Len(log'[CHOOSE i \in Server: \A j \in Server:
                                            Len(log'[i]) >= Len(log'[j])]))
ScrSetTerm              == ("maxTerm" :>
                              currentTerm'[CHOOSE i \in Server: \A j \in Server:
                                            currentTerm'[i] >= currentTerm'[j]])
ScrSetFailure(pc)       ==
    CASE pc[1] = "Timeout: election"   -> ScrClearCont @@ ScrIncTimeout
      [] pc[1] = "Timeout: promote"    -> ScrClearCont @@ ScrIncTimeout
      [] pc[1] = "Restart"             -> ScrClearCont @@ ScrIncRestart
      [] pc[1] = "Drop"                -> ScrClearCont @@ ScrIncDrop
      [] pc[1] = "Duplicate"           -> ScrClearCont @@ ScrIncDup
      [] pc[1] = "NetworkPartition"    -> ScrClearCont
      [] OTHER -> IF ScrIsLocked THEN ScrNoIncCont ELSE ScrIncCont

\* Network partition helpers
ScrIncNetworkCure       == ScrIncHelper("nCure")
ScrSetPartNodes(n)      == ("partNodes" :> GetPartNodes(n))
ScrIsPartitioned        == Cardinality(scr.partNodes) /= 0
ScrNotPartitioned       == ~ScrIsPartitioned
ScrGetPartitionTimes    == IF ScrIsPartitioned THEN scr.nCure + 1 ELSE scr.nCure
ScrNodeConnected(x, y)  ==
    \/ x \notin scr.partNodes /\ y \notin scr.partNodes
    \/ IF GetParameterBool("PartitionDisconnected")
       THEN FALSE
       ELSE x \in scr.partNodes /\ y \in scr.partNodes

\* Check if m is the first msg of m.to
IsFirstMsg(m) ==
    LET myMsg == { i \in messages: i.to = m.to }
        first == CHOOSE i \in myMsg: i.seq <= m.seq
    IN  first = m
\* Increase scr.nRecv and check scr.nUnorder
ScrIncRecvUnorder(m) == IF IsFirstMsg(m) THEN ScrIncRecv
                        ELSE ScrIncRecv @@ ScrIncUnorder

\* Set next state of scr.
\* e.g. ScrSet(ScrIncRecv @@ ScrIncUnorder, "HandleAppendEntriesRequest")
\* WARNING: ScrSet and Scr expr must be placed after UNCHANGED (since it uses
\*          next state). It's better to place UNCHANGED at the first expr.
ScrSet(r, pc) ==
    scr' = r @@ ScrSetWire @@ ScrSetPc(pc) @@ ScrSetInv(InvHelper(pc))
             @@ ScrSetLog  @@ ScrSetTerm   @@ ScrSetFailure(pc) @@ scr
Scr(pc) == ScrSet(ScrSetPc(pc), pc)

SelectSeqWithIdx(s, Test(_,_)) == 
    LET F[i \in 0..Len(s)] == 
        IF i = 0
        THEN <<>>
        ELSE IF Test(s[i], i)
             THEN Append(F[i-1], s[i])
             ELSE F[i-1]
    IN F[Len(s)]

\* Check all inv are true
ScrCheckInv == Len(SelectSeqWithIdx(scr.inv,
                        LAMBDA x, y: ~x /\ y \notin scr.noInv)) = 0

----
\* State constraints.

CheckParameterHelper(n, p, Test(_,_)) ==
    IF p \in DOMAIN Parameters
    THEN Test(n, Parameters[p])
    ELSE TRUE
CheckParameterMax(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i <= j)
\*CheckParameterMin(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i >= j)
PrePrune(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i < j)

ScSent    == CheckParameterMax(scr.nSent,    "MaxSentMsgs")
ScRecv    == CheckParameterMax(scr.nRecv,    "MaxRecvMsgs")
ScWire    == CheckParameterMax(scr.nWire,    "MaxWireMsgs")
ScDrop    == CheckParameterMax(scr.nDrop,    "MaxDropMsgFailures")
ScDup     == CheckParameterMax(scr.nDup,     "MaxDupMsgFailures")
ScUnorder == CheckParameterMax(scr.nUnorder, "MaxUnorderFailures")
ScTimeout == CheckParameterMax(scr.nTimeout, "MaxTimeoutFailures")
ScRestart == CheckParameterMax(scr.nRestart, "MaxRestartFailures")
ScOp      == CheckParameterMax(scr.nOp,      "MaxClientOperations")
ScAe      == CheckParameterMax(scr.nAe,      "MaxHeartbeat")
ScLog     == CheckParameterMax(scr.nLog,     "MaxLogs")
ScTerm    == CheckParameterMax(scr.maxTerm,  "MaxTerm")
ScCont    == CheckParameterMax(scr.nCont,    "MaxContNormalActions")
ScSnap    == CheckParameterMax(scr.nSnapshot,"MaxSnapshot")
ScFailure == CheckParameterMax(scr.nDrop + scr.nDup + scr.nUnorder +
                               scr.nTimeout + scr.nRestart, "MaxFailures")

SC == /\ ScSent    /\ ScRecv    /\ ScWire /\ ScDrop /\ ScDup  /\ ScUnorder
      /\ ScTimeout /\ ScRestart /\ ScOp   /\ ScLog  /\ ScTerm /\ ScCont
      /\ ScFailure /\ ScSnap    /\ ScAe

----
\* Action constraints.

AcCont    == CheckParameterHelper(scr.nCont, "MinContNormalActions",
             LAMBDA i, j: IF i = j \/ ScrIsLocked THEN TRUE ELSE scr'.nCont > 0)

AC == AcCont

----
\* Network

\* Add msg to msgs, increase scr.nMessage.
AddMsg(m, msgs) == LET msgSeq == scr.nSent + 1
                       m_ == IF ScrNodeConnected(m.from, m.to)
                             THEN IF "seq" \in DOMAIN m
                                  THEN {[ m EXCEPT !["seq"] = msgSeq ]}
                                  ELSE {m @@ ( "seq" :> msgSeq )}
                             ELSE {}  \* Dropped.
                   IN msgs \union m_
                   
\* wyy version

\* Add msg to msgs, increase scr.nMessage.
_AddMsgSeq(m, seq, msgs) == LET m_ ==    IF ScrNodeConnected(m.from, m.to)
                                         THEN IF "seq" \in DOMAIN m  \* TODO: add partition, see wraft
                                              THEN {[ m EXCEPT !["seq"] = seq ]}
                                              ELSE {m @@ ( "seq" :> seq )}
                                         ELSE {} \* Dropped.
                           n_ == IF ScrNodeConnected(m.from, m.to)
                                 THEN 1
                                 ELSE 0
                       IN <<n_, msgs \union m_>>

_BatchAddmsgs(ms, msgs)==
    LET F[i \in 0 .. Len(ms)] ==
        IF i = 0 THEN <<0, msgs, <<"msg_batch_add">>>>
        ELSE LET m == ms[i]
                 seq == scr.nSent + F[i-1][1] + 1
                 res == _AddMsgSeq(m, seq ,F[i-1][2])
             IN << res[1] + F[i-1][1], res[2], Append(F[i-1][3],
                    IF res[1] = 1 THEN <<"ok", seq, m.from, m.to>>
                    ELSE <<"dropped", seq, m.from, m.to>>) >>
    IN F[Len(ms)]

\* BatchSendmsgs(ms) == 
\*     LET add == _BatchAddmsgs(ms, messages)
\*         msgs == F[2]
\*         nums == F[1]
\*     IN /\ \* modify scr
\*        /\ messages' = msgs
\*        /\ PrintT(  messages')
\* over 


\* Del msg from msgs.
DelMsg(m, msgs) == IF m \in msgs THEN msgs \ {m} ELSE msgs

\* Do send/discard m.
Send(m)      == messages' = AddMsg(m, messages)
Discard(m)   == messages' = DelMsg(m, messages)
\* Drop/duplicate m.
Drop(m)      == /\ UNCHANGED noNetworkVars
                /\ Discard(m)
                /\ Scr(<<"Drop", Nil, Nil, m.seq>>)
Duplicate(m) == /\ UNCHANGED noNetworkVars
                /\ Send(m)
                /\ ScrSet(ScrIncSent, <<"Duplicate",
                                        Nil, Nil, m.seq, scr.nSent + 1>>)
\* Combination of Send and Discard.
Reply(response, request) ==
    messages' = AddMsg(response, DelMsg(request, messages))
    
ReplyBatchAdd(responses, request) ==
    LET del == DelMsg(request, messages)
        batchadd == _BatchAddmsgs(responses, del)
    IN <<batchadd[1] , batchadd[2]>>

----
\* Init

InitScr ==
    scr = [ nSent |-> 0,   nRecv    |-> 0,   nWire     |-> 0, nDrop    |-> 0,
            nDup  |-> 0,   nUnorder |-> 0,   nTimeout  |-> 0, nRestart |-> 0,
            nOp   |-> 0,   nLog     |-> 0,   maxTerm   |-> 0, inv      |-> <<>>,
            nCure |-> 0,   lock     |-> Nil, nSnapshot |-> 0, partNodes|-> {},
            noInv |-> GetParameterSet("IgnoreInvNumbers"),    nAe      |-> 0 , 
            nCont |-> GetParameter("MinContNormalActions"),   pc |-> <<"Init">>]
InitNetworkVars ==  /\ messages     = {}
InitLogVars     ==  /\ log          = [ i \in Server |-> <<>> ]
                    /\ commitIdx    = [ i \in Server |-> 0 ]
                    /\ logInfo      = [ i \in Server |->
                        [ size |-> IF GetParameter("MinLogCapacity") = 0
                                   THEN 10
                                   ELSE GetParameter("MinLogCapacity"),
                          count |-> 0, front |-> 0, back |-> 0, base |-> 0 ] ]
InitServerVars  ==  \* Init currentTerm to 0, different from ORAFT,
                    \* whose currentTerm is inited to 1.
                    /\ currentTerm  = [ i \in Server |-> 0 ]
                    /\ votedFor     = [ i \in Server |-> Nil ]
                    /\ state        = [ i \in Server |-> Follower ]
InitLeaderVars  ==  /\ nextIdx      = [ i \in Server |-> [ j \in Server |-> 1 ]]
                    /\ matchIdx     = [ i \in Server |-> [ j \in Server |-> 0 ]]
InitCandidateVars  ==  votesGranted = [ i \in Server |-> {} ]
InitSnapshotVars   == /\ snapshotLastIdx  = [ i \in Server |-> 0 ]
                      /\ snapshotLastTerm = [ i \in Server |-> 0 ]

Init == /\ InitScr
        /\ InitNetworkVars
        /\ InitLogVars
        /\ InitServerVars
        /\ InitLeaderVars
        /\ InitCandidateVars
        /\ InitSnapshotVars

----
\* Next

\* TODO: Fix bug: the network partition is strange. It should also use state
\*       constraint instead of checking recovery times.
\* Network partition
NetworkPartition ==
    LET n == GetParameter("PartitionNodes")
    IN IF n = 0
       THEN FALSE
       ELSE /\ UNCHANGED noScrVars
            /\ ScrNotPartitioned
            /\ ScrNotLocked
            /\ LET partnodes == ScrSetPartNodes(n)
               IN ScrSet(partnodes, <<"NetworkPartition", partnodes.partNodes>>)

NetworkRecover ==
    LET n == GetParameter("PartitionRecovery")
        \* If nParted equals server number, ScrNotPartitioned is always false,
        \* NetworkPartition will not be triggered.
        nParted == IF n = scr.nCure + 1 THEN Cardinality(Server) ELSE 0
    IN IF n /= scr.nCure /\ ScrIsPartitioned /\ ScrNotLocked
       THEN /\ UNCHANGED noScrVars
            /\ ScrSet(ScrIncNetworkCure @@ ScrSetPartNodes(nParted),
                        <<"NetworkRecover">>)
       ELSE FALSE

\* Server i restarts. Only currentTerm/votedFor/log restored (i.e. unchanged).
\* NOTE: snapshot variables are considered as parts of log
\* NOTE: last applied index should be cleared here if modelled.
Restart(i) ==
    /\ UNCHANGED <<currentTerm, votedFor, logStoreVars, networkVars,
                   snapshotVars>>
    /\ state'           = [ state           EXCEPT ![i] = Follower ]
    /\ commitIdx'       = [commitIdx        EXCEPT ![i] = snapshotLastIdx[i] ]
    /\ votesGranted'    = [ votesGranted    EXCEPT ![i] = {} ]
    /\ nextIdx'         = [ nextIdx         EXCEPT ![i] = [j \in Server |-> 1 ]]
    /\ matchIdx'        = [ matchIdx        EXCEPT ![i] = [j \in Server |-> 0 ]]
    /\ Scr(<<"Restart", i>>)

\* TODO: This helper is too cumbersome. Improve it.
\* Demote Server i to Follower because term is smaller
BecomeFollowerHelper(i, term, noVote, changeVote, candidate) ==
    /\ state'       = [ state       EXCEPT ![i] = IF \/ /\ candidate
                                                        /\ IsCandidate(i)
                                                        /\ term = currentTerm[i]
                                                     \/ term > currentTerm[i]
                                                  THEN Follower ELSE @ ]
    /\ currentTerm' = [ currentTerm EXCEPT ![i] = IF term > currentTerm[i]
                                                  THEN term     ELSE @ ]
    /\ IF noVote THEN IF changeVote THEN UNCHANGED votedFor ELSE TRUE
       ELSE votedFor' = [ votedFor  EXCEPT ![i] = IF term > currentTerm[i]
                                                  THEN Nil      ELSE @ ]
BecomeFollower(i, term) == BecomeFollowerHelper(i, term, FALSE, TRUE, FALSE)

\* Get lock args: all servers except me, and in set s and parted nodes.
LockArgs(i, s, type) ==
    LET e == {i} \union s
    IN IF e /= Server
       THEN ScrSetLock([ type |-> type, args |-> [ from: {i}, to: Server \ e ]])
       ELSE ScrUnsetLock

\* Send snapshot. Leader i sends j a snapshot.
\* It doesn't really send any snapshots, just sends metadatas.
SendSnapshotHelper(i, j) ==
    LET body    == [ term           |-> currentTerm[i],
                     lastIdx        |-> snapshotLastIdx'[i],
                     lastTerm       |-> snapshotLastTerm'[i] ]
        msg     == [ type           |-> SnapshotRequest,
                     from           |-> i,
                     to             |-> j,
                     body           |-> body ]
    IN msg

\* fix send snapshot instead of sending ae
NeedSnapshot(s, n) == s >= n

SendSnapshot(i, j) ==
    /\ i /= j
    /\ IF NeedSnapshot(snapshotLastIdx[i], nextIdx[i][j])  \* fix
       THEN Send(SendSnapshotHelper(i, j))
       ELSE UNCHANGED networkVars
       
GetSnapshotNoSend(n, preNextIndex) ==
    LET dsts == Server \ {n}
        size == Cardinality(dsts)
        F[i \in 0..size] ==
            IF i = 0 THEN << <<>>, dsts, TRUE>>
            ELSE LET ms == F[i-1][1]
                     s == CHOOSE j \in F[i-1][2]: TRUE
                     nextNodeIdx == preNextIndex[n][s]
                     m == SendSnapshotHelper(n, s)
                     remaining == F[i-1][2] \ {s}
                     flag == F[i-1][3]
                 IN IF flag = TRUE
                    THEN IF NeedSnapshot(snapshotLastIdx'[n], nextNodeIdx)  \* fix
                         THEN <<Append(ms, m), remaining, TRUE>>
                         ELSE <<ms, remaining, TRUE>> 
                    ELSE <<ms, remaining, flag>> 
    IN F[size]

SendSnapshotAllHelper(i) ==  
    LET ret == GetSnapshotNoSend(i, nextIdx)
        ms == ret[1]
        add == _BatchAddmsgs(ms, messages)
    IN add

\* Leader i sends j an AppendEntries/Snapshot request
\* The append entries contain logs from next index to log info back or end.
AppendEntriesHelper(i, j) ==
    IF NeedSnapshot(snapshotLastIdx'[i], nextIdx'[i][j]) THEN SendSnapshotHelper(i, j) ELSE \* fix
    LET entries == IF IsNullEntryIdxNext(i, nextIdx'[i][j])
                   THEN <<>>
                   ELSE GetEntriesForAppendNext(i, nextIdx'[i][j])
        prevEty == GetEntryNext(i, nextIdx'[i][j] - 1)
        body    == [ term           |-> currentTerm[i],
                     leaderCommit   |-> commitIdx'[i],
                     entries        |-> entries,
                     prevLogIdx     |-> IF /\ nextIdx'[i][j] > 1
                                           /\ IsNullEntry(prevEty)
                                        THEN snapshotLastIdx'[i]
                                        ELSE nextIdx'[i][j] - 1,
                     prevLogTerm    |-> IF IsNullEntry(prevEty)
                                        THEN snapshotLastTerm'[i]
                                        ELSE prevEty.term ]
        msg     == [ type           |-> AppendEntriesRequest,
                     from           |-> i,
                     to             |-> j,
                     body           |-> body ]
    IN msg

AppendEntries(i, j) == i /= j /\ Send(AppendEntriesHelper(i, j))


\* wyy version
GetAppendEntriesNoSend(n, preNextIndex) ==
    LET dsts == Server \ {n}
        size == Cardinality(dsts)
        F[i \in 0..size] ==
            IF i = 0 THEN << <<>>, dsts, TRUE>>
            ELSE LET ms == F[i-1][1]
                     s == CHOOSE j \in F[i-1][2]: TRUE
                     nextNodeIdx == preNextIndex[n][s]
                     curLog == log'[n]
                     m == AppendEntriesHelper(n, s)
                     remaining == F[i-1][2] \ {s}
                     flag == F[i-1][3]
                 IN IF flag = TRUE
                    THEN IF snapshotLastIdx'[n] <= nextNodeIdx
                         THEN <<Append(ms, m), remaining, TRUE>>
                         ELSE <<Append(ms, m), remaining, FALSE>>
                    ELSE <<ms,remaining, flag>>
    IN F[size]

GetAppendEntriesExceptBehindIdxNoSend(n, preNextIndex, idx) ==
    LET dsts == Server \ {n}
        size == Cardinality(dsts)
        F[i \in 0..size] ==
            IF i = 0 THEN << <<>>, dsts>>
            ELSE LET ms == F[i-1][1]
                     s == CHOOSE j \in F[i-1][2]: TRUE
                     nextNodeIdx == preNextIndex[n][s]
                     m == AppendEntriesHelper(n, s)
                     remaining == F[i-1][2] \ {s}
                 IN IF nextNodeIdx = idx
                    THEN <<Append(ms, m), remaining>>
                    ELSE <<ms, remaining>>
    IN F[size]

\* CHANGED: netVars, nextIndex
SendAppendEntries(n) == 
    LET ret == GetAppendEntriesNoSend(n, nextIdx)
        ms == ret[1]
        leftServers == ret[2]
        add == _BatchAddmsgs(ms, messages)
    IN add

SendAppendEntriesExceptBehindIdx(n, idx) ==
    LET ret == GetAppendEntriesExceptBehindIdxNoSend(n, nextIdx, idx)
        ms == ret[1]
        leftServers == ret[2]
        add == _BatchAddmsgs(ms, messages)
    IN add

AppendEntriesAll(i) ==
    LET all == SendAppendEntries(i)
    IN /\ UNCHANGED noNetworkVars
       /\ IsLeader(i)
       /\ messages' = all[2]
       /\ ScrSet( NetIncBy("nSent", all[1]) @@ ScrIncAe, <<"AppendEntriesAll", i>>)

\* over

\* Send RequestVoteRequest to all servers except me and servers in set s.
\*RequestVoteAll(i) ==
\*    LET s == LockArgs(i, {}, RequestVoteRequest)
\*    IN ScrSet(s, <<"Timeout: election", i>>)

\* wyy version
\* RequestVoteAll
RequestVoteAll(n) ==
    LET  dsts == Server \ {n}
         size == Cardinality(dsts)
         F[i \in 0..size] == 
            IF i = 0 THEN << <<>>, dsts>>
            ELSE LET ms == F[i-1][1]
                     s == CHOOSE j \in F[i-1][2] : TRUE
                     body == [ term          |-> currentTerm'[n],
                              candidate     |-> n,
                              lastLogIdx    |-> LastIdx(n),
                              lastLogTerm   |-> LastTerm(n) ]
                     msg  == [ type |-> RequestVoteRequest,
                              from |-> n,
                              to   |-> s,
                              body |-> body ]
                     remaining == F[i-1][2] \ {s}
                 IN <<Append(ms, msg), remaining>>
         add == _BatchAddmsgs(F[size][1], messages)
    IN /\ messages' = add[2]
       /\ ScrSet(NetIncBy("nSent", add[1]), <<"Timeout: election", n>>)
    
\* over

\* Send AppendEntriesRequest to all servers except me.
\*AppendEntriesAll(i) ==
\*    /\ UNCHANGED noScrVars
\*    /\ IsLeader(i)
\*    /\ LET s == LockArgs(i, {}, AppendEntriesRequest) @@ ScrIncAe
\*       IN /\ s.lock /= Nil
\*          /\ ScrSet(s, <<"AppendEntriesAll", i>>)

\* Send AppendEntriesRequest to all servers except fall behind servers.
AppendEntriesExceptBehindIdx(i, idx) ==
    LET e == { j \in Server \ {i}: nextIdx[i][j] /= idx }
        s == LockArgs(i, e, AppendEntriesRequest)
    IN ScrSet(s @@ ScrIncOp, <<"ClientRequest", i>>)

\* fix
\* Server i receives an AppendEntries request from server j.
HandleAppendEntriesRequest(i, j, m) ==
    LET b   == m.body
        rb1 == [ term       |-> currentTerm'[i],
                 success    |-> FALSE,
                 curIdx     |-> LastIdxNext(i) ]
        rb2 == [ term       |-> currentTerm'[i],
                 success    |-> TRUE,
                 curIdx     |-> b.prevLogIdx + Len(b.entries) ]
        msg == [ type       |-> AppendEntriesResponse,
                 from       |-> i,
                 to         |-> j ]  \* Body is not included here.
    IN IF b.term < currentTerm[i]    \* Term is smaller, reply false.
       THEN /\ UNCHANGED noNetworkVars
            /\ Reply(msg @@ ("body" :> rb1), m)
            /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                        <<"HandleAppendEntriesRequest: stale msg",
                          i, j, m.seq, scr.nSent + 1, FALSE>>)
       ELSE /\ BecomeFollowerHelper(i, b.term, FALSE, TRUE, TRUE)
            /\ IF b.prevLogIdx > LastIdx(i)  \* would leave gap
               THEN /\ UNCHANGED <<candidateVars, leaderVars, logVars,
                                   snapshotVars>>
                    /\ Reply(msg @@ ("body" :> rb1), m)
                    /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                              <<"HandleAppendEntriesRequest: would leave gap",
                                i, j, m.seq, scr.nSent + 1, FALSE>>)
               ELSE IF /\ ~IsNullEntryIdx(i, b.prevLogIdx)
                       /\ NotEqualEntryTerm(i, b.prevLogIdx, b.prevLogTerm)
                    THEN \* log mismatch
                         /\ UNCHANGED <<candidateVars, leaderVars, commitIdx,
                                        snapshotVars>>
                         /\ LET tmp == GetEntriesToIdx(i, b.prevLogIdx - 1)
                                n   == LogLen(i) - Len(tmp)
                                tp  == LogPopEntriesHelper(log[i], logInfo[i], n)
                            IN LogUpdate(i, tp)
                         /\ Reply(msg @@ ("body" :> rb1), m)
                         /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                                   <<"HandleAppendEntriesRequest: log mismatch",
                                     i, j, m.seq, scr.nSent + 1, FALSE>>)
                    ELSE \* Prev log 1. matches, 2. is a snapshot, 3. is 0
                         /\ UNCHANGED <<candidateVars, leaderVars, snapshotVars>>
                         /\ IF Len(b.entries) = 0
                            THEN UNCHANGED logStoreVars
                            ELSE LogUpdate(i, GetMatchEntries(i, b.entries,
                                                              b.prevLogIdx))
                         \* Check if commitIdx can be advanced.
                         /\ commitIdx' = [ commitIdx EXCEPT ![i] =
                                           IF commitIdx[i] >= b.leaderCommit
                                           THEN @  \* Not updated.
                                           ELSE Min({b.leaderCommit} \union
                                                    {Max({LastIdxNext(i), 1})})]
                         /\ Reply(msg @@ ("body" :> rb2), m)
                         /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                                     <<"HandleAppendEntriesRequest: success",
                                       i, j, m.seq, scr.nSent + 1, TRUE>>)

\* Advance commmitIdx.
AdvanceCommitIdx(s, idx) ==
    LET c1 == commitIdx[s] < idx /\ ~NotEqualEntryTerm(s, idx, currentTerm[s])
        c2 == IsQuorum({i \in Server \ {s}: matchIdx'[s][i] >= idx} \union {s})
    IN commitIdx' = [ commitIdx EXCEPT ![s] = IF c1 /\ c2 THEN idx ELSE @ ]

\* Server i receives an AppendEntries response from server j.
HandleAppendEntriesResponse(i, j, m) == 
    LET b          == m.body
        not_leader == ~IsLeader(i)
        demote     == currentTerm[i] < b.term
        stale_msg  == \/ currentTerm[i] > b.term
                      \/ /\ ~b.success
                         /\ matchIdx[i][j] = nextIdx[i][j] - 1
                      \/ /\ b.success
                         /\ b.curIdx <= matchIdx[i][j]
        retry      == /\ ~b.success
                      /\ b.curIdx >= matchIdx[i][j]
    IN IF not_leader
       THEN /\ UNCHANGED noNetworkVars
            /\ Discard(m)
            /\ ScrSet(ScrIncRecvUnorder(m),
                    <<"HandleAppendEntriesResponse: not leader",
                      i, j, m.seq, Nil, FALSE>>)
       ELSE IF demote
            THEN /\ UNCHANGED <<candidateVars, leaderVars, logVars,
                                snapshotVars>>
                 /\ Discard(m)
                 /\ BecomeFollower(i, b.term)
                 /\ ScrSet(ScrIncRecvUnorder(m),
                        <<"HandleAppendEntriesResponse: demote",
                          i, j, m.seq, Nil, FALSE>>)
            ELSE IF stale_msg
                 THEN /\ UNCHANGED noNetworkVars
                      /\ Discard(m)
                      /\ ScrSet(ScrIncRecvUnorder(m),
                            <<"HandleAppendEntriesResponse: stale msg",
                              i, j, m.seq, Nil, FALSE>>)
                 ELSE IF retry
                      THEN \* AppendEntries failed, update nextIdx and retry.
                           /\ UNCHANGED <<serverVars, candidateVars, matchIdx,
                                          logVars, snapshotVars>>
                           /\ nextIdx' = [ nextIdx EXCEPT ![i][j] =
                                    IF b.curIdx < @ - 1
                                    THEN Max({1, Min({b.curIdx + 1, LastIdx(i)})})
                                    ELSE Max({1, @ - 1}) ]
                           /\ Reply(AppendEntriesHelper(i, j), m)
                           /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                                <<"HandleAppendEntriesResponse: mismatch and retry",
                                  i, j, m.seq, scr.nSent + 1, FALSE>>)
                      ELSE \* AppendEntries succeeded
                           /\ UNCHANGED <<serverVars, candidateVars,
                                          logStoreVars, snapshotVars>>
                           /\ nextIdx' = [ nextIdx EXCEPT ![i][j] = b.curIdx+1 ]
                           /\ matchIdx' = [ matchIdx EXCEPT ![i][j] = b.curIdx ]
                           /\ AdvanceCommitIdx(i, b.curIdx)
                           /\ IF IsNullEntryIdx(i, nextIdx'[i][j])
                              THEN /\ Discard(m)
                                   /\ ScrSet(ScrIncRecvUnorder(m),
                                        <<"HandleAppendEntriesResponse: success",
                                          i, j, m.seq, Nil, TRUE>>)
                              ELSE \* Aggressively send remainings.
                                   /\ Reply(AppendEntriesHelper(i, j), m)
                                   /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                                        <<"HandleAppendEntriesResponse: success and append more",
                                          i, j, m.seq, scr.nSent + 1, TRUE>>)

\* Candidate i sends j a RequestVote request.
RequestVote(i, j) ==
    LET body == [ term          |-> currentTerm'[i],
                  candidate     |-> i,
                  lastLogIdx    |-> LastIdx(i),
                  lastLogTerm   |-> LastTerm(i) ]
        msg  == [ type |-> RequestVoteRequest,
                  from |-> i,
                  to   |-> j,
                  body |-> body ]
    IN Send(msg)

\* Server i receives a RequestVote request from server j.
\* Note: WRAFT code checks if timeElapsed >= electionTimeout * 1. TLA+ doesn't
\*       model timeout and servers are always votable.
HandleRequestVoteRequest(i, j, m) ==
    LET body        == m.body
        voteNil     == \/ votedFor[i] = Nil
                       \/ body.term > currentTerm[i]
        lastEty     == GetEntry(i, LastIdx(i))
        logCmp(t)   == \/ body.lastLogTerm > t
                       \/ /\ body.lastLogTerm = t
                          /\ body.lastLogIdx >= LastIdx(i)
        logOk       == \/ LastIdx(i) = 0
                       \/ IF lastEty /= Nil THEN logCmp(LastTerm(i))
                          ELSE /\ snapshotLastIdx[i] = LastIdx(i)
                               /\ logCmp(snapshotLastTerm[i])
        canGrant    == /\ ~IsLeader(i)
                       /\ body.term >= currentTerm'[i]
                       /\ voteNil
                       /\ logOk
        rb          == [ term |-> currentTerm'[i], voteGranted |-> canGrant ]
        msg         == [ type |-> RequestVoteResponse,
                         from |-> i,
                         to   |-> j,
                         body |-> rb ]
    IN IF IsLeader(i)
       THEN /\ UNCHANGED noNetworkVars
            /\ Reply(msg, m)
            /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                            <<"HandleRequestVoteRequest: leader not granted",
                              i, j, m.seq, scr.nSent + 1, FALSE>>)
       ELSE /\ UNCHANGED <<candidateVars, leaderVars, logVars, snapshotVars>>
            /\ BecomeFollowerHelper(i, body.term, canGrant, FALSE, FALSE)
            /\ Reply(msg, m)
            /\ IF canGrant
               THEN /\ votedFor' = [ votedFor EXCEPT ![i] = j ]
                    /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                                 <<"HandleRequestVoteRequest: granted",
                                   i, j, m.seq, scr.nSent + 1, TRUE>>)
               ELSE /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                                 <<"HandleRequestVoteRequest: not granted",
                                   i, j, m.seq, scr.nSent + 1, FALSE>>)

\* Become Leader.
BecomeLeader(i) ==
    /\ state'    = [ state    EXCEPT ![i] = Leader ]
    /\ nextIdx'  = [ nextIdx  EXCEPT ![i] =
                       [ j \in Server |-> IF i = j THEN 1 ELSE LastIdx(i) + 1 ]]
    /\ matchIdx' = [ matchIdx EXCEPT ![i] = [ j \in Server |-> 0 ]]

\* Server i receives a RequestVote response from server j.
HandleRequestVoteResponse(i, j, m) ==
    /\ LET b == m.body
           notCandidate == ~IsCandidate(i)
           staleMsg     == currentTerm[i] > b.term
           notGranted   == currentTerm[i] = b.term /\ ~b.voteGranted
       IN IF notCandidate \/ staleMsg \/ notGranted
          THEN /\ UNCHANGED noNetworkVars
               /\ Discard(m)
               /\ ScrSet(ScrIncRecvUnorder(m),
                    <<CASE notCandidate -> "HandleRequestVoteResponse: not candidate"
                        [] staleMsg     -> "HandleRequestVoteResponse: stale msg"
                        [] notGranted   -> "HandleRequestVoteResponse: not granted"
                        [] OTHER        -> Assert(FALSE,
                           "HandleRequestVoteResponse unhandled CASE"),
                      i, j, m.seq, FALSE>>)
          ELSE IF currentTerm[i] < b.term
               THEN /\ UNCHANGED <<candidateVars, leaderVars, logVars,
                                   snapshotVars>>
                    /\ BecomeFollower(i, b.term)
                    /\ Discard(m)
                    /\ ScrSet(ScrIncRecvUnorder(m),
                                <<"HandleRequestVoteResponse: demote",
                                  i, j, m.seq, FALSE>>)
               ELSE /\ votesGranted' = [ votesGranted EXCEPT ![i] =
                                            @ \union {j}]
                    /\ IF IsQuorum(votesGranted'[i])
                       THEN LET replyBatch == ReplyBatchAdd(GetAppendEntriesNoSend(i, nextIdx')[1], m)
                            IN 
                            /\ UNCHANGED <<currentTerm, votedFor, logVars,
                                           snapshotVars>>
                            /\ BecomeLeader(i)
                            \* Note: sends append entries immediately
                            /\ messages' = replyBatch[2]
                            \* /\ SendAppendEntries(i)
                            /\ ScrSet(NetIncBy("nSent", replyBatch[1]) @@ ScrIncRecvUnorder(m),
                                      <<"HandleRequestVoteResponse: promote",
                                        i, j, m.seq, TRUE>>)
                       ELSE /\ UNCHANGED <<serverVars, leaderVars, logVars,
                                           snapshotVars>>
                            /\ Discard(m)
                            /\ ScrSet(ScrIncRecvUnorder(m),
                                        <<"HandleRequestVoteResponse: get vote",
                                          i, j, m.seq, TRUE>>)

\* fix
\* Handle snapshot request
HandleSnapshotRequest(i, j, m) ==
    LET b   == m.body
        rb1 == [ term       |-> currentTerm[i],
                 success    |-> FALSE,
                 curIdx     |-> LastIdxNext(i) ]
        rb2 == [ term       |-> currentTerm'[i],
                 success    |-> TRUE,
                 curIdx     |-> b.lastIdx ]
        msg == [ type       |-> AppendEntriesResponse,
                 from       |-> i,
                 to         |-> j,
                 body       |-> rb2 ]
    IN IF \/ b.term < currentTerm[i]
          \/ b.lastIdx <= 0
          \/ b.lastTerm = 0
          \/ /\ b.lastIdx <= LastIdx(i)
             /\ b.lastIdx /= snapshotLastIdx[i]
             /\ IsNullEntryIdx(i, b.lastIdx)
       THEN /\ UNCHANGED noNetworkVars
            /\ Reply([ msg EXCEPT !["body"] = rb1 ], m)
            /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                        <<"HandleSnapshotRequest: stale msg",
                          i, j, m.seq, scr.nSent + 1, FALSE>>)
       ELSE IF /\ b.lastIdx <= LastIdx(i)
               /\ \/ b.lastIdx = snapshotLastIdx[i]
                  \/ GetEntry(i, b.lastIdx).term = b.lastTerm
            THEN /\ UNCHANGED noNetworkVars
                 /\ Reply([ msg EXCEPT !["body"] = rb2 ], m)
                 /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                                <<"HandleSnapshotRequest: unnecessary",
                                  i, j, m.seq, scr.nSent + 1, TRUE>>)
            ELSE /\ UNCHANGED <<candidateVars, leaderVars>>
                 /\ LogLoadFromSnapshot(i, b.lastIdx)
                 /\ IF currentTerm[i] < b.lastTerm
                    THEN /\ currentTerm' = [ currentTerm EXCEPT ![i] = b.lastTerm ]
                         /\ votedFor'    = [ votedFor    EXCEPT ![i] = Nil ]
                    ELSE UNCHANGED <<currentTerm, votedFor>>
                 /\ state' = [ state EXCEPT ![i] = Follower ]
                 /\ IF commitIdx[i] < b.lastIdx
                    THEN commitIdx' = [ commitIdx EXCEPT ![i] = b.lastIdx ]
                    ELSE UNCHANGED commitIdx
                 /\ snapshotLastIdx'  = [ snapshotLastIdx  EXCEPT ![i] = b.lastIdx ]
                 /\ snapshotLastTerm' = [ snapshotLastTerm EXCEPT ![i] = b.lastTerm ]
                 /\ Reply(msg, m)
                 /\ ScrSet(ScrIncSent @@ ScrIncRecvUnorder(m),
                             <<"HandleSnapshotRequest: success",
                               i, j, m.seq, scr.nSent + 1, TRUE>>)

\* Begin snapshot
BeginSnapshot(i) ==
    LET isSnapshottable == /\ commitIdx[i] > logInfo[i].base
                           /\ LogLen(i) > 1
        target          == commitIdx[i]
        ety             == GetEntry(i, target)
    IN \* TLA doesn't model an FSM to apply logs
       /\ isSnapshottable
       /\ snapshotLastTerm' = [ snapshotLastTerm EXCEPT ![i] = ety.term ]
       /\ snapshotLastIdx'  = [ snapshotLastIdx  EXCEPT ![i] = target ]

\* End snapshot
EndSnapshot(i) == LogPollEntries(i, snapshotLastIdx'[i] - logInfo[i].base)

\* Do snapshot
ExecSnapshot(i) ==
    /\ UNCHANGED <<serverVars, candidateVars, leaderVars,
                   commitIdx>>
    /\ BeginSnapshot(i)
    /\ EndSnapshot(i)
    /\ IF IsLeader(i)
       THEN LET all == SendSnapshotAllHelper(i)
            IN  /\ messages' = all[2]
                /\ ScrSet(NetIncBy("nSent", all[1]) @@ ScrIncSnapshot, 
                        <<"ExecSnapshot: leader", i, commitIdx[i]>>) 
       ELSE /\ UNCHANGED messages
            /\ ScrSet(ScrIncSnapshot,
                    <<"ExecSnapshot: not leader", i, commitIdx[i]>>)
            

\* Loop send AppendEntriesRequest/RequestVoteRequest/SnapshotRequest
DoLoop ==
    /\ UNCHANGED noNetworkVars
    /\ ScrIsLocked
    /\ Cardinality(scr.lock.args) /= 0
    /\ LET a  == CHOOSE x \in scr.lock.args: TRUE
           t  == ScrGetLockType
           s  == ScrDeleteLockArg(a) @@ ScrIncSent
           ok == ScrNodeConnected(a.from, a.to)
       IN CASE t = AppendEntriesRequest ->
                    /\ AppendEntries(a.from, a.to)
                    /\ LET c == snapshotLastIdx[a.from] > nextIdx[a.from][a.to]
                           x == IF c \* Cancel subsequent sendings
                                THEN ScrUnsetLock @@ ScrIncSent
                                ELSE s
                       IN ScrSet(x, <<"DoLoop: AppendEntries", a.from, a.to,
                                       scr.nSent + 1, ok>>)
            [] t = RequestVoteRequest   ->
                    /\ RequestVote(a.from, a.to)
                    /\ ScrSet(s, <<"DoLoop: RequestVote",   a.from, a.to,
                              scr.nSent + 1, ok>>)
            [] t = SnapshotRequest      ->
                    /\ SendSnapshot (a.from, a.to)
                    /\ IF snapshotLastIdx[a.from] > nextIdx[a.from][a.to]
                       THEN ScrSet(s, <<"DoLoop: SendSnapshot",
                                        a.from, a.to, scr.nSent + 1, ok>>)
                       ELSE Assert(FALSE, <<"DoLoop bad send", a.from>>)
            [] OTHER -> Assert(FALSE, "DoLoop unhandled CASE")

\* Server i times out and start a new election.
BecomeCandidate(i) ==
    /\ state'           = [ state           EXCEPT ![i] = Candidate ]
    /\ currentTerm'     = [ currentTerm     EXCEPT ![i] = @ + 1 ]
    \* Set the local vote atomically.
    /\ votedFor'        = [ votedFor        EXCEPT ![i] = i ]
    /\ votesGranted'    = [ votesGranted    EXCEPT ![i] = {i} ]
    /\ RequestVoteAll(i)

\* Election timeout, become candidate and send request vote
Timeout(i) == /\ ~IsLeader(i)
              /\ IF Cardinality(Server) > 1
                 THEN /\ UNCHANGED << leaderVars, logVars,
                                     snapshotVars>>
                      /\ BecomeCandidate(i)
                 ELSE /\ UNCHANGED <<networkVars, currentTerm, votedFor,
                                     candidateVars, logVars, snapshotVars>>
                      /\ BecomeLeader(i)
                      /\ Scr(<<"Timeout: promote", i>>)

\* Receive a msg m from network.
Receive(m) ==
    LET t == m.type
        i == m.to
        j == m.from
    IN /\ CASE t = AppendEntriesRequest  -> HandleAppendEntriesRequest (i, j, m)
            [] t = AppendEntriesResponse -> HandleAppendEntriesResponse(i, j, m)
            [] t = RequestVoteRequest    -> HandleRequestVoteRequest   (i, j, m)
            [] t = RequestVoteResponse   -> HandleRequestVoteResponse  (i, j, m)
            [] t = SnapshotRequest       -> HandleSnapshotRequest      (i, j, m)
            [] OTHER -> Assert(FALSE, "Receive unhandled CASE")
       /\ Assert(i /= j, "Receive i = j")

\* Leader i receives a client request.
ClientRequest(i, v) ==
    LET all == SendAppendEntriesExceptBehindIdx(i, LastIdxNext(i))
    IN  /\ IsLeader(i)
        /\ LogAppendEntries(i, <<[ term |-> currentTerm[i], value |-> v ]>>)
        /\ IF Cardinality(Server) = 1
           THEN /\ commitIdx' = [ commitIdx EXCEPT ![i] = @ + 1 ]
                /\ UNCHANGED <<serverVars, candidateVars, leaderVars,
                                snapshotVars>>
           ELSE UNCHANGED <<noLogVars>>
        /\ messages' = all[2]
        /\ ScrSet( NetIncBy("nSent", all[1]) @@ ScrIncOp, <<"ClientRequest", i, v>>)

\* Send AppendEntriesRequest to all servers except fall behind servers.

----
\* Next transition.

\* Define these helpers to see coverage more conveniently.
DoHandleAppendEntriesRequest    == \E m \in messages:
                                    m.type = AppendEntriesRequest  /\ Receive(m)
DoHandleAppendEntriesResponse   == \E m \in messages:
                                    m.type = AppendEntriesResponse /\ Receive(m)
DoHandleRequestVoteRequest      == \E m \in messages:
                                    m.type = RequestVoteRequest    /\ Receive(m)
DoHandleRequestVoteResponse     == \E m \in messages:
                                    m.type = RequestVoteResponse   /\ Receive(m)
DoHandleSnapshotRequest         == \E m \in messages:
                                    m.type = SnapshotRequest       /\ Receive(m)
DoAppendEntriesAll              == PrePrune(scr.nAe, "MaxHeartbeat") /\ \E i \in Server:
                                    AppendEntriesAll(i)
DoClientRequest                 == PrePrune(scr.nOp, "MaxClientOperations") /\ \E i \in Server, v \in Value:
                                    ClientRequest(i, v)
DoTimeout                       == PrePrune(scr.nTimeout, "MaxTimeoutFailures") /\ \E i \in Server:
                                    Timeout(i)
DoRestart                       == PrePrune(scr.nRestart, "MaxRestartFailures") /\ \E i \in Server:
                                    Restart(i)
DoDrop                          == PrePrune(scr.nDrop, "MaxDropMsgFailures") /\ \E m \in messages :
                                    Drop(m)
DoDuplicate                     == PrePrune(scr.nDup, "MaxDupMsgFailures") /\ \E m \in messages :
                                    Duplicate(m)
DoSnapshot                      == PrePrune(scr.nSnapshot, "MaxSnapshot") /\ \E i \in Server:
                                    ExecSnapshot(i)

Next == \/ DoHandleAppendEntriesRequest
        \/ DoHandleAppendEntriesResponse
        \/ DoHandleRequestVoteRequest
        \/ DoHandleRequestVoteResponse
        \/ DoHandleSnapshotRequest
        \/ DoAppendEntriesAll
        \/ DoClientRequest
        \/ DoSnapshot
        \/ DoTimeout
        \* \/ DoRestart
        \* \/ DoDrop
        \* \/ DoDuplicate
        \* \/ DoLoop
        \/ NetworkPartition
        \/ NetworkRecover

vars == <<noScrVars, scr>>

Spec == Init /\ [][Next]_vars

----
\* Invarients

\* Delegated to ScrCheckInv
Inv == ScrCheckInv

=============================================================================
\* Modification History
\* Last modified Tue Apr 25 15:58:22 CST 2023 by wego
\* Created Mon Apr 24 18:40:12 CST 2023 by wego

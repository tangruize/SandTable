----------------------------- MODULE PySyncObj -----------------------------

EXTENDS Sequences, Naturals, Integers, FiniteSets, TLC

(***************************************************************************
  Constants definitions
 ***************************************************************************)
CONSTANTS Servers                      \* Servers set
CONSTANTS Follower, Candidate, Leader  \* Server states
CONSTANTS Commands, NoOp               \* Commands set
CONSTANTS M_RV, M_RVR, M_AE,           \* Raft message types
          M_NNI                       \* Non-Standard message types (AER is NNI)
\*          ,M_AC, M_ACR                  \* Apply command (clients send cmd to Leader, not modelled)
CONSTANTS Parameters, Nil  \* Misc: state constraint parameters and placeholder

(***************************************************************************
  Variables definitions
 ***************************************************************************)
VARIABLES currentTerm, votedFor, log  \* Persistent variables
VARIABLES raftState, commitIndex      \* Volatile variables
VARIABLES nextIndex, matchIndex       \* Leader variables
VARIABLES votesCount                  \* Candidate variables

(***************************************************************************
  Network variables and instance
 ***************************************************************************)
VARIABLES netman, netcmd, msgs
INSTANCE FifoNetwork WITH FLUSH_DISCONN <- TRUE, NULL_MSG <- Nil,
    _msgs <- msgs, _netman <- netman, _netcmd <- netcmd

(***************************************************************************
  Self manipulated invariants checking
 ***************************************************************************)
VARIABLES inv

(***************************************************************************
  Type Ok
 ***************************************************************************)
TypeOkServerVars ==
    /\ currentTerm \in [ Servers -> Nat ]
    /\ votedFor    \in [ Servers -> Servers \cup {Nil} ]
    /\ raftState   \in [ Servers -> { Follower, Candidate, Leader } ]
TypeOkLeaderVars ==
    /\ nextIndex   \in [ Servers -> [ Servers -> Nat \ {0} ]]
    /\ matchIndex  \in [ Servers -> [ Servers -> Nat ]]
TypeOkCandidateVars ==
    /\ votesCount  \in [ Servers -> 0..Cardinality(Servers) ]
TypeOkLogVars ==
    \* log data structure is complex, we skip checking it
    /\ commitIndex \in [ Servers -> Nat \ {0} ]
TypeOk ==
    /\ TypeOkServerVars
    /\ TypeOkLeaderVars
    /\ TypeOkCandidateVars
    /\ TypeOkLogVars

(***************************************************************************
  Init variables
 ***************************************************************************)
InitServerVars ==
    /\ currentTerm = [ i \in Servers |-> 0 ]
    /\ votedFor    = [ i \in Servers |-> Nil ]
    /\ raftState   = [ i \in Servers |-> Follower ]
InitLeaderVars ==
\*    /\ nextIndex  = [ i \in Servers |-> [ j \in Servers \ {i} |-> 1 ]]
\*    /\ matchIndex = [ i \in Servers |-> [ j \in Servers \ {i} |-> 0 ]]
    /\ nextIndex  = [ i \in Servers |-> [ j \in Servers |-> 1 ]]
    /\ matchIndex = [ i \in Servers |-> [ j \in Servers |-> 0 ]]
InitCandidateVars ==
    \* Q: Directly count?
    /\ votesCount = [ i \in Servers |-> 0 ]
InitLogVars ==
    \* Q: Why No-Op added?
    /\ log = [ i \in Servers |-> <<[ cmd |-> NoOp, idx |-> 1, term |-> 0 ]>> ]
    \* Q: Init to 1?
    /\ commitIndex = [ i \in Servers |-> 1 ]
InitInv == inv = <<>>

\*GetParameter(p)     == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE 0
\*GetParameterBool(p) == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE FALSE
GetParameterSet(p)  == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE {}

Init ==
    /\ InitServerVars
    /\ InitLeaderVars
    /\ InitCandidateVars
    /\ InitLogVars
\*    /\ InitFifoNetwork(Servers)
\* op: client op, ae: append entry RPC times, n_elec: election timeout times
    /\ InitFifoNetworkAddNetman(Servers, <<"init", Cardinality(Servers)>>, 
            [ n_op |-> 0, n_ae |-> 0, n_elec |-> 0, no_inv |-> GetParameterSet("no_inv")])
    /\ InitInv

(***************************************************************************
  Helper functions
 ***************************************************************************)
\* Variable type sequences
serverVars    == <<currentTerm, votedFor, raftState>>
leaderVars    == <<nextIndex, matchIndex>>
candidateVars == <<votesCount>>
logVars       == <<log, commitIndex>>
netVars       == <<netman, netcmd, msgs>>
noNetVars     == <<serverVars, leaderVars, candidateVars, logVars>>
vars          == <<noNetVars, netVars, inv>>

CheckStateIs(n,  s)   == raftState[n] = s
CheckStateIsNot(n, s) == raftState[n] /= s
SetState(n, s)        == raftState' = [ raftState EXCEPT ![n] = s ]

GetCurrentTerm(n)    == currentTerm[n]
GetCurrentLog(n)     == log[n][Len(log[n])]
GetCurrentLogTerm(n) == GetCurrentLog(n).term
GetCurrentLogIdx(n)  == GetCurrentLog(n).idx
AddCurrentTerm(n)    == currentTerm' = [ currentTerm EXCEPT ![n] = @+1 ]
SetCurrentTerm(n, t) == currentTerm' = [ currentTerm EXCEPT ![n] = t ]

SetCommitIdx(n, idx) == commitIndex' = [ commitIndex EXCEPT ![n] = idx ]
GetCommitIdx(n)      == commitIndex[n]

GetVotedFor(n)       == votedFor[n]
SetVotedFor(n, v)    == votedFor' = [ votedFor EXCEPT ![n] = v ] \*CHANGED: votedFor
CheckNotVoted(n)     == GetVotedFor(n) = Nil
CheckTermNotVoted(n) ==
    IF currentTerm'[n] > GetCurrentTerm(n) THEN TRUE ELSE GetVotedFor(n) = Nil

CheckTermBecomeFollower(n, term) ==
    IF term > GetCurrentTerm(n)
    THEN /\ SetCurrentTerm(n, term)
         /\ SetState(n, Follower)
\*         /\ SetVotedFor(n, Nil)  \* caution votedFor will change
    ELSE UNCHANGED <<currentTerm, raftState>>

AddVotesCount(n) ==
    votesCount' = [ votesCount EXCEPT ![n] = @+1 ]
CheckVotesCountIsQuorum(n) ==
    votesCount'[n] * 2 > Cardinality(Servers)
ResetCandidateVotesCount(n) ==
    votesCount' = [ votesCount EXCEPT ![n] = 1 ]

GetEntriesFromLog(curLog, prev) ==
    LET firstEntryIdx == curLog[1].idx
    IN IF prev < firstEntryIdx THEN <<>>
       ELSE LET diff == prev - firstEntryIdx
            IN SubSeq(curLog, diff + 1, Len(curLog))
GetEntriesFrom(n, prev) ==
    LET curLog        == log[n]
    IN GetEntriesFromLog(curLog, prev)
DeleteEntriesFrom(n, from) ==
    LET curLog == log[n]
        firstEntryIdx == curLog[1].idx
    IN IF from < firstEntryIdx THEN curLog
       ELSE LET diff == from - firstEntryIdx
            IN SubSeq(curLog, 1, diff)

GetPrevLog(curLog, nextIdx) ==
    LET entries == GetEntriesFromLog(curLog, nextIdx - 1)
    IN IF Len(entries) /= 0 THEN entries[1] ELSE Nil
GetPrevLogIdx(curLog, nextIdx) ==
    LET prevLog == GetPrevLog(curLog, nextIdx)
    IN IF prevLog /= Nil THEN nextIdx - 1 ELSE Nil
GetPrevLogTerm(curLog, nextIdx) ==
    LET prevLog == GetPrevLog(curLog, nextIdx)
    IN IF prevLog /= Nil THEN prevLog.term ELSE Nil

IsDemoted(n) == currentTerm[n] /= currentTerm'[n]

MsgGetFieldDefault(m, field, default) ==
    IF field \in DOMAIN m THEN m[field] ELSE default

MsgGetField(m, field) == MsgGetFieldDefault(m, field, Nil)

LogAppendEntry(n, v) ==
    LET curLog == log[n]
        len == Len(curLog)
        term == currentTerm[n]
        idx == curLog[len].idx + 1
    IN Append(curLog, [ cmd |-> v, idx |-> idx, term |-> term])

IsQuorum(ss) == Cardinality(ss) * 2 > Cardinality(Servers)

UpdateNextIndex(n) ==
    nextIndex' = [ nextIndex EXCEPT ![n] =
                   [ j \in Servers |-> IF @[j] <= log'[n][Len(log'[n])].idx
                                       THEN log'[n][Len(log'[n])].idx + 1
                                       ELSE @[j] ]]

Min(x,y) == IF x < y THEN x ELSE y

(***************************************************************************)
(* Send append entries                                                     *)
(***************************************************************************)
\* (should be placed after UNCHANGED because) Depending on currentTerm', commitIndex', log', nextIndex'
GetAppendEntriesNoSend(n, preNextIndex) == 
    LET dsts == Servers \ {n}
        size == Cardinality(dsts)
        F[i \in 0..size] ==
                IF i = 0 THEN <<<<>>, dsts>>
                ELSE LET ms == F[i-1][1]
                         s == CHOOSE j \in F[i-1][2]: TRUE
                         nextNodeIdx == preNextIndex[n][s]
                         curLog == log'[n]
                         m == [ src  |-> n, dst |-> s, type |-> M_AE,
                                data |-> [ term |-> currentTerm'[n],
                                           commitIdx |-> commitIndex'[n],
                                           entries |-> GetEntriesFromLog(curLog, nextNodeIdx),
                                           prevLogIdx |-> GetPrevLogIdx(curLog, nextNodeIdx),
                                           prevLogTerm |-> GetPrevLogTerm(curLog, nextNodeIdx)]]
                         remaining == F[i-1][2] \ {s}
                     IN <<Append(ms, m), remaining>>
    IN F[size]
\*    IN /\ NetUpdate2(NetBatchAddMsg(F[size][1]), <<"SendAppendEntries", n>>)
\*       /\ Assert(Cardinality(F[size][2]) = 0, <<"SendAppendEntries bug", F>>)

\* CHANGED: netVars, nextIndex
SendAppendEntriesIncNetman(n, field) == 
    LET ret == GetAppendEntriesNoSend(n, nextIndex)
        m == ret[1]
        leftServers == ret[2]
    IN /\ NetUpdate2(NetmanIncField(field, NetBatchAddMsg(m)), <<"SendAppendEntries", n>>)
       /\ UpdateNextIndex(n)
       /\ Assert(Cardinality(leftServers) = 0, <<"SendAppendEntries bug", ret>>)

SendAppendEntries(n) == SendAppendEntriesIncNetman(n, "n_ae")

(***************************************************************************)
(* Client request                                                          *)
(***************************************************************************)
ClientRequest(n, v) ==
    /\ CheckStateIs(n, Leader)
    /\ log' = [ log EXCEPT ![n] = LogAppendEntry(n, v) ]
    /\ UpdateNextIndex(n)
    /\ UNCHANGED <<serverVars, matchIndex, candidateVars, commitIndex>>
    /\ LET toSend == GetAppendEntriesNoSend(n, nextIndex)
           m == toSend[1]
       IN NetUpdate2(NetmanIncField("n_op", NetBatchAddMsg(m)), <<"ClientRequest", n, v>>)

(***************************************************************************)
(*   Raft message handling                                                 *)
(***************************************************************************)
HandleMsgRV(m) ==
    LET data == m.data
        src  == m.src
        dst  == m.dst
    IN /\ CheckTermBecomeFollower(dst, data.term) \* CHANGED: currentTerm, raftState
       /\ IF /\ raftState'[dst] /= Leader     \* is not leader
             /\ data.term >= currentTerm'[dst]   \* term is smaller or equal
             /\ ~(\/ data.lastLogTerm < GetCurrentLogTerm(dst)  \* log is out dated
                  \/ /\ data.lastLogTerm = GetCurrentLogTerm(dst)
                     /\ data.lastLogIdx  < GetCurrentLogIdx(dst)
                  \/ (IF IsDemoted(dst) THEN FALSE ELSE ~CheckTermNotVoted(dst) ))    \* already voted
          THEN \* CHANGED: votedFor
               /\ SetVotedFor(dst, src)          \* vote
               /\ UNCHANGED <<leaderVars, candidateVars, logVars>>
               /\ LET reply == [ type |-> M_RVR, \* reply
                                 data |-> [ term |-> data.term ]]
                  IN NetUpdate2(NetReplyMsg(reply, m), <<"HandleMsgRV", "voted", dst, src>>)
           ELSE /\ IF IsDemoted(dst) THEN SetVotedFor(dst, Nil) ELSE UNCHANGED votedFor
                /\ UNCHANGED <<leaderVars, candidateVars, logVars>>
                /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRV", "not-voted", dst, src>>) \* receive and dequeue msg

HandleMsgRVR(m) ==
    LET data == m.data
        src  == m.src
        dst  == m.dst
    IN /\ IF /\ CheckStateIs(dst, Candidate)
             /\ data.term = GetCurrentTerm(dst)
          THEN /\ AddVotesCount(dst)  \* CHANGED: votesCount
               /\ IF CheckVotesCountIsQuorum(dst)
                  THEN \* CHANGED: raftState, nextIndex, matchIndex, log
                       /\ log' = [ log EXCEPT ![dst] = LogAppendEntry(dst, NoOp)]
                       /\ raftState'  = [ raftState EXCEPT ![dst] = Leader ]
\*                       /\ UpdateNextIndex(dst)
                       /\ nextIndex' = [ nextIndex EXCEPT ![dst] = [ j \in Servers |-> log'[dst][Len(log'[dst])].idx + 1 ]]
                       /\ matchIndex' = [ matchIndex EXCEPT ![dst] =
\*                           [ j \in Servers \ {dst} |-> 0 ]]
                             [ j \in Servers |-> 0 ]]
                       /\ UNCHANGED <<currentTerm, votedFor, commitIndex>>
                       /\ LET preNextIndex == [ nextIndex' EXCEPT ![dst] = [ j \in Servers |-> @[j] - 1 ]]
                          IN NetUpdate2(NetReplyBatchAddMsg(GetAppendEntriesNoSend(dst, preNextIndex)[1], m),
                                     <<"HandleMsgRVR", "become-leader-and-send-append-entries", dst, src>>)
                  ELSE /\ UNCHANGED <<currentTerm, votedFor, commitIndex, leaderVars, log, raftState>>
                       /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRVR", "not-quorum", dst, src>>)
          ELSE /\ UNCHANGED <<currentTerm, votedFor, commitIndex, raftState, candidateVars, leaderVars, log>>
               /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRVR", "not-candidate-or-term-not-equal", dst, src>>)
\*       /\ UNCHANGED <<currentTerm, votedFor, commitIndex>>
\*       /\ UNCHANGED <<currentTerm, votedFor, logVars>>
\*       /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRVR", dst, src>>)

HandleMsgAE(m) ==
LET data      == m.data
    src       == m.src
    dst       == m.dst
    commitIdx == data.commitIdx
IN\/ /\ data.term < GetCurrentTerm(dst)
     /\ UNCHANGED noNetVars
     /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgAE", "term-is-smaller", dst, src>>)
  \/ /\ data.term >= GetCurrentTerm(dst)
       \* CHANGED: raftState, commitIndex
     /\/\ IF data.term > GetCurrentTerm(dst)
          THEN  \* CHANGED: currentTerm, votedFor
               /\ SetCurrentTerm(dst, data.term)  
               /\ SetVotedFor(dst, Nil)
          ELSE UNCHANGED <<currentTerm, votedFor>>
       /\ SetState(dst, Follower)
       /\ UNCHANGED <<leaderVars, candidateVars>>
       /\ IF "prevLogIdx" \in DOMAIN data  \* append entries
          THEN LET prevLogIdx  == data.prevLogIdx
                   prevLogTerm == data.prevLogTerm
                   prevEntries == GetEntriesFrom(dst, prevLogIdx)
               IN IF Len(prevEntries) = 0  \* log mismatch (missing)
                  THEN /\ LET reply == [ type |-> M_NNI,  \* next node idx
                                         data |-> [ success |-> FALSE, reset |-> TRUE, nextNodeIdx |-> GetCurrentLogIdx(dst) + 1 ] ]
                          IN NetUpdate2(NetReplyMsg(reply, m), <<"HandleMsgAE", "no-prevEntries", dst, src>>)
                       /\ UNCHANGED logVars
                  ELSE IF prevEntries[1].term /= prevLogTerm  \* log mismatch (term not equal)
                       THEN /\ LET reply == [ type |-> M_NNI,  \* next node idx
                                             data |-> [ nextNodeIdx |-> prevLogIdx, success |-> FALSE, reset |-> TRUE ] ]
                               IN NetUpdate2(NetReplyMsg(reply, m), <<"HandleMsgAE", "term-mismatch", dst, src>>)
                            /\ UNCHANGED logVars
                       ELSE \* CHANGED: log, commitIndex
                            /\ LET afterDeleteLog == DeleteEntriesFrom(dst, prevLogIdx + 1)
                                   entries        == data.entries
                                   nextNodeIdx    == IF Len(entries) = 0 THEN prevLogIdx + 1 ELSE entries[Len(entries)].idx
                                   reply          == [ type |-> M_NNI,  \* next node idx
                                                       data |-> [ nextNodeIdx |-> nextNodeIdx, success |-> TRUE ] ]
                               IN /\ log' = [ log EXCEPT ![dst] = afterDeleteLog \o entries ]
                                  /\ NetUpdate2(NetReplyMsg(reply, m), <<"HandleMsgAE", "success", dst, src>>)
                            /\ IF commitIdx > GetCommitIdx(dst)
                               THEN SetCommitIdx(dst, Min(commitIdx, log'[dst][Len(log'[dst])].idx))
                               ELSE UNCHANGED commitIndex
          ELSE /\ TRUE \* install snapshot (not implemented)
               /\ Assert(FALSE, "Not implemented!")
               /\ UNCHANGED log

TryAdvanceCommitIdx(s, idx) ==
    LET c1 == commitIndex[s] < idx \*/\ GetEntriesFrom(s, idx)[1].term = currentTerm[s]
        c2 == IsQuorum({i \in Servers \ {s}: matchIndex'[s][i] >= idx} \union {s})
    IN commitIndex' = [ commitIndex EXCEPT ![s] = IF c1 /\ c2 THEN idx ELSE @ ]

HandleMsgNNI(m) ==
    LET data == m.data
        src == m.src
        dst == m.dst
        reset == MsgGetField(data, "reset")
        nextNodeIdx == MsgGetField(data, "nextNodeIdx")
        currentNodeIdx == nextNodeIdx - 1
        success == MsgGetField(data, "success")
    IN /\ IF CheckStateIs(dst, Leader)
          THEN /\ IF reset = TRUE THEN nextIndex' = [ nextIndex EXCEPT ![dst][src] = nextNodeIdx ]
                  ELSE UNCHANGED nextIndex
               /\ IF success = TRUE THEN matchIndex' = [ matchIndex EXCEPT ![dst][src] = currentNodeIdx ]
                  ELSE UNCHANGED matchIndex
               /\ TryAdvanceCommitIdx(dst, matchIndex'[dst][src])
               /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgNNI", IF reset = TRUE THEN "reset" ELSE "success", dst, src>>)
          ELSE /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgNNI", "not-leader", dst, src>>)
               /\ UNCHANGED <<matchIndex, nextIndex, commitIndex>>
       /\ UNCHANGED <<serverVars, candidateVars, log>>

(***************************************************************************
  Election timeout and become candidate
 ***************************************************************************)
ElectionTimeout(n) ==
    /\ SetState(n, Candidate)
    /\ AddCurrentTerm(n)
    /\ ResetCandidateVotesCount(n)
    /\ SetVotedFor(n, n)
    /\ LET dsts == Servers \ {n}
           size == Cardinality(dsts)
           F[i \in 0..size] ==
                IF i = 0 THEN <<<<>>, dsts>>
                ELSE LET ms == F[i-1][1]
                         s == CHOOSE j \in F[i-1][2]: TRUE
                         m == [ src  |-> n, dst |-> s, type |-> M_RV,
                                data |-> [ term |-> currentTerm'[n],
                                           lastLogIdx  |-> GetCurrentLogIdx(n),
                                           lastLogTerm |-> GetCurrentLogTerm(n) ]]
                         remaining == F[i-1][2] \ {s}
                     IN <<Append(ms, m), remaining>>
       IN /\ NetUpdate2(NetmanIncField("n_elec", NetBatchAddMsg(F[size][1])), <<"ElectionTimeout", n>>)
          /\ Assert(Cardinality(F[size][2]) = 0, <<"ElectionTimeout bug", F>>)
          /\ UNCHANGED <<leaderVars, logVars>>

(***************************************************************************
  Invariants
 ***************************************************************************)
ElectionSafety ==
    LET TwoLeader ==
            \E i, j \in Servers:
                /\ i /= j
                /\ currentTerm[i] = currentTerm[j]
                /\ raftState[i] = Leader
                /\ raftState[j] = Leader
    IN ~TwoLeader

LeaderAppendOnly ==
  ~UNCHANGED log =>
    \A i \in Servers:
        IF raftState[i] = Leader /\ raftState'[i] = Leader
        THEN LET curLog == log[i]
                 nextLog == log'[i]
             IN IF Len(nextLog) >= Len(curLog)
                THEN SubSeq(nextLog, 1, Len(curLog)) = curLog
                ELSE FALSE
        ELSE TRUE

LogMatching ==
    \A i, j \in Servers:
        IF i /= j
        THEN LET iLog == log[i]
                 jLog == log[j]
                 len == Min(Len(iLog), Len(jLog))
                 F[k \in 0..len] ==
                    IF k = 0 THEN <<>>
                    ELSE LET key1 == <<iLog[k].term, iLog[k].idx>>
                             value1 == iLog[k].cmd
                             key2 == <<jLog[k].term, jLog[k].idx>>
                             value2 == jLog[k].cmd
                             F1 == IF key1 \in DOMAIN F[k-1]
                                   THEN IF F[k-1][key1] = value1 THEN F[k-1] ELSE F[k-1] @@ ( <<-1, -1>> :> <<key1, value1, F[k-1][key1]>> )
                                   ELSE F[k-1] @@ (key1 :> value1)
                             F2 == IF key2 \in DOMAIN F1
                                   THEN IF F1[key2] = value2 THEN F1 ELSE F1 @@ ( <<-1, -1>> :> <<key2, value2, F1[key2]>> )
                                   ELSE F1 @@ (key2 :> value2)
                         IN F2
             IN <<-1, -1>> \notin DOMAIN F[len]
        ELSE TRUE

MonotonicCurrentTerm ==
  ~UNCHANGED currentTerm =>
    \A i \in Servers: currentTerm' [i] >= currentTerm[i]

MonotonicCommitIdx ==
  ~UNCHANGED commitIndex =>
    \A i \in Servers: commitIndex'[i] >= commitIndex[i]

MonotonicMatchIdx ==
  ~UNCHANGED matchIndex =>
    \A i \in Servers:
        IF raftState[i] = Leader
        THEN \A j \in Servers:  matchIndex'[i][j] >= matchIndex[i][j]
        ELSE TRUE

SelectSeqWithIdx(s, Test(_,_)) == 
    LET F[i \in 0..Len(s)] == 
        IF i = 0
        THEN <<>>
        ELSE IF Test(s[i], i)
             THEN Append(F[i-1], s[i])
             ELSE F[i-1]
    IN F[Len(s)]

NextIdxGtMatchIdx ==
  ~UNCHANGED <<nextIndex, matchIndex>> =>
    \A i \in Servers: raftState[i] = Leader =>
        \A j \in Servers \ {i}: nextIndex'[i][j] > matchIndex'[i][j]

InvSequence == <<
    LeaderAppendOnly,
    MonotonicCurrentTerm,
    MonotonicCommitIdx,
    MonotonicMatchIdx,
    NextIdxGtMatchIdx
>>

INV == Len(SelectSeqWithIdx(inv, LAMBDA x, y: ~x /\ y \notin netman.no_inv)) = 0

(***************************************************************************
  State constraints
 ***************************************************************************)

\*CONSTANTS MaxSentMsgs,
\*          MaxRecvMsgs,
\*          MaxWireMsgs,
\*          MaxPartitionTimes,
\*          MaxCureTimes,
\*          MaxClientOperationsTimes,
\*          MaxAppenEntriesTimes,
\*          MaxElectionTimes,
\*          MaxLogLength,
\*          MaxTerm

CheckParameterHelper(n, p, Test(_,_)) ==
    IF p \in DOMAIN Parameters
    THEN Test(n, Parameters[p])
    ELSE TRUE
CheckParameterMax(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i <= j)

GetRealLogLen(curLog) == SelectSeq(curLog, LAMBDA i: i.cmd /= NoOp)
GetMaxLogLen == Len(log[CHOOSE i \in Servers: \A j \in Servers:  GetRealLogLen(log[i]) >= GetRealLogLen(log[j])])
GetMaxTerm   == currentTerm[CHOOSE i \in Servers: \A j \in Servers: currentTerm[i] >= currentTerm[j]]

ScSent == CheckParameterMax(netman.n_sent, "MaxSentMsgs")
ScRecv == CheckParameterMax(netman.n_recv, "MaxRecvMsgs")
ScWire == CheckParameterMax(netman.n_wire, "MaxWireMsgs")
ScLog  == CheckParameterMax(GetMaxLogLen,  "MaxLogLength")
ScTerm == CheckParameterMax(GetMaxTerm,    "MaxTerm")

ScPart == CheckParameterMax(netman.n_part, "MaxPartitionTimes")
ScCure == CheckParameterMax(netman.n_cure, "MaxCureTimes")
ScOp   == CheckParameterMax(netman.n_op,   "MaxClientOperationsTimes")
ScAe   == CheckParameterMax(netman.n_ae,   "MaxAppenEntriesTimes")
ScElec == CheckParameterMax(netman.n_elec, "MaxElectionTimes")

SC == /\ ScSent /\ ScRecv /\ ScWire /\ ScLog /\ ScTerm
\*      /\ ScPart /\ ScCure /\ ScOp /\ ScAe /\ ScElec

PrePrune(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i < j)

 (***************************************************************************
  Next actions
 ***************************************************************************)
DoHandleMsgRV ==
    /\ \E src, dst \in Servers:
        /\ src /= dst
        /\ LET m == NetGetMsg(src, dst)
           IN /\ m /= Nil
              /\ m.type = M_RV
              /\ HandleMsgRV(m)
    /\ inv' = InvSequence

DoHandleMsgRVR ==
    /\ \E src \in Servers, dst \in Servers:
        /\ src /= dst
        /\ LET m == NetGetMsg(src, dst)
           IN /\ m /= Nil
              /\ m.type = M_RVR
              /\ HandleMsgRVR(m)
    /\ inv' = InvSequence

DoHandleMsgAE ==
    /\ \E src \in Servers, dst \in Servers:
        /\ src /= dst
        /\ LET m == NetGetMsg(src, dst)
           IN /\ m /= Nil
              /\ m.type = M_AE
              /\ HandleMsgAE(m)
    /\ inv' = InvSequence

DoHandleMsgNNI ==
    /\ \E src \in Servers, dst \in Servers:
        /\ src /= dst
        /\ LET m == NetGetMsg(src, dst)
           IN /\ m /= Nil
              /\ m.type = M_NNI
              /\ HandleMsgNNI(m)
    /\ inv' = InvSequence

DoElectionTimeout ==
    /\ PrePrune(netman.n_elec, "MaxElectionTimes")
    /\ \E n \in Servers: CheckStateIsNot(n, Leader) /\ ElectionTimeout(n)
    /\ inv' = InvSequence

DoNetworkPartition ==
    /\ PrePrune(netman.n_part, "MaxPartitionTimes")
    /\ \E n \in Servers:
        /\ NetUpdate2(NetPartConn({n}), <<"DoNetworkPartition", n>>)
        /\ UNCHANGED noNetVars
    /\ inv' = InvSequence

DoNetworkCure ==
    /\ PrePrune(netman.n_cure, "MaxCureTimes")
    /\ NetIsParted
    /\ NetUpdate2(NetCureConn, <<"DoNetworkCure">>)
    /\ UNCHANGED noNetVars
    /\ inv' = InvSequence

DoClientRequest ==
    /\ PrePrune(netman.n_op,   "MaxClientOperationsTimes")
    /\ \E n \in Servers, v \in Commands:
        ClientRequest(n, v)
    /\ inv' = InvSequence

DoSendAppendEntries ==
    /\ PrePrune(netman.n_ae,   "MaxAppenEntriesTimes")
    /\ \E n \in Servers: /\ CheckStateIs(n, Leader)
                         /\ UNCHANGED <<serverVars, matchIndex, candidateVars, logVars>>
                         /\ SendAppendEntries(n)
    /\ inv' = InvSequence

Next == \*/\ 
           \/ DoElectionTimeout
           \/ DoClientRequest
           \/ DoSendAppendEntries
           \/ DoHandleMsgRV
           \/ DoHandleMsgRVR
           \/ DoHandleMsgAE
           \/ DoHandleMsgNNI
           \/ DoNetworkPartition
           \/ DoNetworkCure
\*        /\ inv' = InvSequence

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Tue Nov 22 16:36:48 CST 2022 by tangruize
\* Created Wed Jul 06 13:50:24 CST 2022 by tangruize

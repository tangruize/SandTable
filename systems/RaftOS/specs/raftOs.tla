---- MODULE raftOs ----
EXTENDS Naturals, FiniteSets, Sequences, Integers, TLC

\* The set of server IDs
CONSTANT Servers

\* The set of requests that can go into the log
CONSTANT Commands, NoOp

CONSTANTS Follower, Candidate, Leader \* Server states

CONSTANTS RV, RVR, 
            AE, AER  \* Raft message types

CONSTANTS  Parameters, Nil  \* Misc: state constraint parameters and placeholder

(***************************************************************************
  Variables definitions
 ***************************************************************************)
VARIABLES currentTerm, votedFor, log  \* Persistent variables
VARIABLES raftState, commitIndex      \* Volatile variables
VARIABLES nextIndex, matchIndex       \* Leader variables
VARIABLES votesGranted                  \* Candidate variables
VARIABLES inv


(***************************************************************************
  Network variables and instance
 ***************************************************************************)
VARIABLES netman, netcmd, msgs
INSTANCE UdpNetwork WITH  NULL_MSG <- Nil,
    _msgs <- msgs, _netman <- netman, _netcmd <- netcmd


TypeOkServerVars == 
    /\ currentTerm \in [ Servers -> Nat ]
    /\ votedFor    \in [ Servers -> Servers \cup {Nil} ]
    /\ raftState   \in [ Servers -> { Follower, Candidate, Leader } ] 

TypeOkLeaderVars ==
    /\ nextIndex   \in [ Servers -> [ Servers -> Nat \ {0} ]]
    /\ matchIndex  \in [ Servers -> [ Servers -> Nat ]]

\* TypeOkCandidateVars ==
\*     /\ votesGranted  \in [ Servers -> {} ]
    
TypeOkLogVars ==
    \* log data structure is complex, we skip checking it
    /\ commitIndex \in [ Servers -> Nat   ]

TypeOk ==
    /\ TypeOkServerVars
    /\ TypeOkLeaderVars
    /\ TypeOkLogVars


(***************************************************************************
  Init variables
 ***************************************************************************)
InitServerVars ==
    /\ currentTerm = [ i \in Servers |-> 0 ]
    /\ votedFor    = [ i \in Servers |-> Nil ]
    /\ raftState   = [ i \in Servers |-> Follower ]

InitLeaderVars ==
    /\ nextIndex  = [ i \in Servers |-> [ j \in Servers |-> 1 ]]
    /\ matchIndex = [ i \in Servers |-> [ j \in Servers |-> 0 ]]

InitCandidateVars ==
    \* Q: Directly count?
    /\ votesGranted = [ i \in Servers |-> {} ]

InitLogVars ==
    \* Q: Why No-Op added?
    /\ log = [ i \in Servers |-> << >> ]
    \* 
    /\ commitIndex = [ i \in Servers |-> 0 ]
InitInv == inv = <<>>

GetParameterSet(p)  == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE {}

Init ==
    /\ InitServerVars
    /\ InitLeaderVars
    /\ InitCandidateVars
    /\ InitLogVars
    /\ InitInv
    /\ InitUdpNetworkNetman(Servers, <<"Init", Cardinality(Servers)>>, 
                [n_elec |-> 0, n_ae |-> 0, n_op |-> 0, no_inv |-> {}, n_restart |-> 0, n_drop |-> 0, n_dup |-> 0])


\* Variable type sequences
serverVars == <<currentTerm, votedFor, raftState>>
leaderVars == <<nextIndex, matchIndex>>
candidateVars == <<votesGranted>>
logVars == <<log, commitIndex>>
netVars == <<netman, netcmd, msgs>>
noNetVars     == <<serverVars, leaderVars, candidateVars, logVars>>
vars          == <<noNetVars, netVars, inv>>



(***************************************************************************
  Helper functions
 ***************************************************************************)
Min(x,y) == IF x < y THEN x ELSE y

Max(x,y) == IF x < y THEN y ELSE x

IsQuorum(ss) == Cardinality(ss) * 2 > Cardinality(Servers)

CheckStateIs(n,  s)   == raftState[n] = s
CheckStateIsNot(n, s) == raftState[n] /= s
SetState(n, s)        == raftState' = [ raftState EXCEPT ![n] = s ]

GetCurrentTerm(n)    == currentTerm[n]
GetCurrentLastLog(n)     == IF Len(log[n]) /= 0 
                            THEN log[n][Len(log[n])] 
                            ELSE << >> \* the last of the n server
GetCurrentLastLogTerm(n) == IF Len(log[n]) /= 0 
                            THEN GetCurrentLastLog(n).term
                            ELSE 0
GetCurrentLastLogIdx(n)  ==  Len(log[n])
AddCurrentTerm(n)    == currentTerm' = [ currentTerm EXCEPT ![n] = @+1 ]
SetCurrentTerm(n, t) == currentTerm' = [ currentTerm EXCEPT ![n] = t ]

SetCommitIdx(n, idx) == commitIndex' = [ commitIndex EXCEPT ![n] = idx ]
GetCommitIdx(n)      == commitIndex[n]

GetVotedFor(n)       == votedFor[n]
SetVotedFor(n, v)    == votedFor' = [ votedFor EXCEPT ![n] = v ] \*CHANGED: votedFor
CheckNotVoted(n)     == GetVotedFor(n) = Nil
CheckTermNotVoted(n) ==
    IF currentTerm'[n] > GetCurrentTerm(n) THEN TRUE ELSE CheckNotVoted(n)
    
IsDemoted(n) == currentTerm[n] /= currentTerm'[n]
    
UpdateNextIndex(n) == 
    IF Len(log'[n]) > 0
    THEN nextIndex' = [ nextIndex EXCEPT ![n] =
                   [ j \in Servers |-> IF @[j] <= log'[n][Len(log'[n])].idx
                                       THEN log'[n][Len(log'[n])].idx + 1
                                       ELSE @[j] ]]
    ELSE nextIndex' =[ nextIndex EXCEPT ![n] =
                   [ j \in Servers |-> 1]]
    


AddVotesGranted(n, j) ==
    votesGranted' = [ votesGranted EXCEPT ![n] = votesGranted[n] \cup {j}]
ResetCandidateVotesGranted(n) ==
    votesGranted' = [ votesGranted EXCEPT ![n] = {} ]
CheckVoteGrantedIsQuorum(n) == IsQuorum(votesGranted'[n]) 

CheckTermBecomeFollower(n, term) ==
    IF term > GetCurrentTerm(n)
    THEN /\ SetCurrentTerm(n, term)
         /\ SetState(n, Follower)
\*         /\ SetVotedFor(n, Nil)  \* caution votedFor will change
    ELSE UNCHANGED <<currentTerm, raftState>>
    
\* here consider snapshot, in raftos firstEntryIdx = 1, seems have no impact
GetEntriesFromLog(curLog, prev) ==
    IF Len(curLog) = 0
    THEN << >> 
    ELSE IF prev < 1 THEN <<>>
                 ELSE SubSeq(curLog, prev, Len(curLog))


\* here consider snapshot, in raftos firstEntryIdx = 1, seems have no impact
GetOneEntryFromLog(curLog, prev) ==
    IF Len(curLog) = 0
    THEN <<>> 
    ELSE IF prev < 1 THEN <<>>
                 ELSE IF prev > Len(curLog)
                      THEN <<>>
                      ELSE <<curLog[prev]>>

GetEntriesFrom(n, prev) ==
    LET curLog        == log[n]
    IN IF Len(curLog) > 0 
       THEN GetEntriesFromLog(curLog, prev)
       ELSE curLog

DeleteEntriesFrom(n, from) ==
    LET curLog == log[n]
        lastIdx == GetCurrentLastLogIdx(n)
    IN IF from > lastIdx THEN curLog
       ELSE SubSeq(curLog, 1, from)

GetPrevLog(curLog, nextIdx) ==
    LET entries == GetEntriesFromLog(curLog, nextIdx - 1)
    IN IF Len(entries) /=  0 THEN entries[1] ELSE Nil
GetPrevLogIdx(curLog, nextIdx) ==
    LET prevLog == GetPrevLog(curLog, nextIdx)
    IN IF prevLog /= Nil THEN nextIdx - 1 ELSE 0
GetPrevLogTerm(curLog, nextIdx) ==
    LET prevLog == GetPrevLog(curLog, nextIdx)
    IN IF prevLog /= Nil THEN prevLog.term ELSE 0

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

\* (should be placed after UNCHANGED because) Depending on currentTerm', commitIndex', log', nextIndex'
\* may be something wrong
\* get append entries msgs to other server
GetAppendEntriesNoSend(n, preNextIndex) ==
    LET dsts == Servers \ {n}
        size == Cardinality(dsts)
        F[i \in 0..size] ==
            IF i = 0 THEN << <<>>, dsts>>
            ELSE LET ms == F[i-1][1]
                     s == CHOOSE j \in F[i-1][2]: TRUE
                     nextNodeIdx == preNextIndex[n][s]
                     curLog == log'[n]
                     m == [src |-> n, dst |-> s, type |-> AE,
                            data |-> [term |-> currentTerm'[n], 
                                        commitIndex |-> commitIndex'[n], 
                                        entries |-> GetOneEntryFromLog(curLog, nextNodeIdx),
                                        prevLogIdx |-> GetPrevLogIdx(curLog, nextNodeIdx),
                                        prevLogTerm |-> GetPrevLogTerm(curLog, nextNodeIdx)]]
                     remaining == F[i-1][2] \ {s}
                 IN <<Append(ms, m), remaining>>
    IN F[size]

\* CHANGED: netVars, nextIndex
SendAppendEntriesIncNetman(n, field) == 
    LET ret == GetAppendEntriesNoSend(n, nextIndex)
        ms == ret[1]
        leftServers == ret[2]
    IN /\ NetUpdate2(NetmanIncField(field, NetBatchAddMsg(ms)),
            <<"SendAppendEntries", n>>)
       /\ Assert(Cardinality(leftServers) = 0, 
                <<"SendAppendEntries bug", ret>>)

SendAppendEntries(n) == SendAppendEntriesIncNetman(n, "n_ae")


LogAppendEntry(n, v) ==
    LET curLog == log[n]
        len == Len(curLog)
        term == currentTerm[n]
\*        idx == curLog[len].idx + 1
    IN Append(curLog, [ cmd |-> v, idx |-> len + 1, term |-> term])


\* Return the minimum value from a set, or undefined if the set is empty.
MinInSet(s) == CHOOSE x \in s : \A y \in s : x <= y

\* Return the maximum value from a set, or undefined if the set is empty.
MaxInSet(s) == CHOOSE x \in s : \A y \in s : x >= y




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


\* GetMaxLogLen == Len(log[CHOOSE i \in Servers: \A j \in Servers:  GetRealLogLen(log[i]) >= GetRealLogLen(log[j])])
\* GetMaxTerm   == currentTerm[CHOOSE i \in Servers: \A j \in Servers: currentTerm[i] >= currentTerm[j]]


ScElec == CheckParameterMax(netman.n_elec, "MaxElectionTimes")

ScSent == CheckParameterMax(netman.n_sent, "MaxSentMsgs")
ScRecv == CheckParameterMax(netman.n_recv, "MaxRecvMsgs")
ScWire == CheckParameterMax(netman.n_wire, "MaxWireMsgs")
\* ScLog  == CheckParameterMax(GetMaxLogLen,  "MaxLogLength")
\* ScTerm == CheckParameterMax(GetMaxTerm,    "MaxTerm")


SC == /\ ScSent /\ ScRecv /\ ScWire 
\*      /\ ScPart /\ ScCure /\ ScOp /\ ScAe /\ ScElec

PrePrune(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i < j)



(***************************************************************************)
(*   Raft message handling                                                 *)
(***************************************************************************)

Restart(i) ==
    /\ SetState(i, Follower)
    /\ votesGranted'   = [votesGranted EXCEPT ![i] = {}]
    /\ nextIndex'      = [nextIndex EXCEPT ![i] = [j \in Servers |-> 1]]
    /\ matchIndex'     = [matchIndex EXCEPT ![i] = [j \in Servers |-> 0]]
    /\ SetCommitIdx(i, 0)
    /\ NetUpdate2(NetmanIncFieldWithoutUpdate("n_restart"),<<"Restart", i>>)
    /\ UNCHANGED <<msgs, currentTerm, votedFor, log>>

TimeOut(n) == 
    /\ SetState(n, Candidate)
    /\ AddCurrentTerm(n)
    /\ votedFor' = [votedFor EXCEPT ![n] = n]
    /\ votesGranted' = [votesGranted EXCEPT ![n] = {n}]
    /\ LET  dsts == Servers \ {n}
            size == Cardinality(dsts)
            F[i \in 0..size] == 
                IF i = 0 THEN << <<>>, dsts>>
                ELSE LET ms == F[i-1][1]
                         s == CHOOSE j \in F[i-1][2] : TRUE
                         m == [src |-> n, dst |-> s, type |-> RV,
                                data |-> [term |-> currentTerm'[n],
                                          lastLogIdx |-> GetCurrentLastLogIdx(n),
                                          lastLogTerm |-> GetCurrentLastLogTerm(n)]]
                         remaining == F[i-1][2] \ {s}
                     IN <<Append(ms, m), remaining>>
       IN NetUpdate2(NetmanIncField("n_elec", NetBatchAddMsg(F[size][1])),
                        <<"ElectionTimeout", n>>)
    /\ UNCHANGED <<leaderVars, logVars>>




\* i = recipient, j = sender, m = message

\* Server i receives a RequestVote request from server j with
\* m.mterm <= currentTerm[i].
\* cause drop stale message may put other message in, we check another time
HandleMsgRV(i, j, m) == 
    /\ m.type = RV
    /\   LET data == m.data
             voteLegal == \/ votedFor[i] = Nil
                          \/ /\ data.term > currentTerm[i]
                             /\ raftState[i] /= Follower
             logOk == \/ data.lastLogTerm > GetCurrentLastLogTerm(i)
                      \/ /\ data.lastLogTerm = GetCurrentLastLogTerm(i)
                         /\ data.lastLogIdx >= GetCurrentLastLogIdx(i)
             grant == /\ data.term >= currentTerm'[i]
                      /\ logOk
             rb  == [ term |-> currentTerm'[i], voteGranted |-> grant, success |-> TRUE]
             reply == [ type |-> RVR,
                      src |-> i,
                      dst |-> j,
                      data |-> rb ]
        IN /\ data.term >= currentTerm[i]
           /\ IF raftState[i] = Follower
              THEN /\ data.term >= currentTerm[i]
                   /\ SetCurrentTerm(i, data.term)
                   /\ UNCHANGED << raftState>>
                   /\ IF    /\ raftState'[i] /= Leader
                            /\ data.term >= currentTerm'[i]
                            /\ voteLegal
                            \* already voted 
                      THEN 
                            /\ \/  grant /\ votedFor' = [votedFor EXCEPT ![i] = j]
                               \/ ~grant /\ UNCHANGED votedFor
                            /\ NetUpdate2(NetReplyMsg(reply, m), <<"HandleMsgRV", "msg valid", j, i, m.seq>>)
                            /\ UNCHANGED<< candidateVars, leaderVars, logVars>>  
                      ELSE /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRV", "stale msg", j, i, m.seq>>)
                           /\ UNCHANGED<< candidateVars, leaderVars, logVars, votedFor>> 
              ELSE IF data.term > currentTerm[i]
                   THEN /\ CheckTermBecomeFollower(i, data.term)
                        /\ SetVotedFor(i, Nil)
                        /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRV", "to follower", j, i, m.seq>>)
                        /\ UNCHANGED << candidateVars, leaderVars, logVars>>  
                   ELSE /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRV", "stale msg", j, i, m.seq>>)
                        /\ UNCHANGED <<noNetVars>>  

BecomeLeader(i) ==
    /\ SetState(i, Leader)
    /\ nextIndex'  = [ nextIndex  EXCEPT ![i] =
                       [ j \in Servers |-> IF i = j THEN 1 ELSE GetCurrentLastLogIdx(i) + 1 ]]
    /\ matchIndex' = [ matchIndex EXCEPT ![i] = [ j \in Servers |-> 0 ]]



\* Server i receives a RequestVote response from server j with
\* m.mterm = currentTerm[i].
HandleMsgRVR(i, j, m) ==
    LET data == m.data
    IN IF raftState[i] /= Follower
       THEN IF data.term > currentTerm[i]
            THEN /\ SetCurrentTerm(i, data.term)
                 /\ SetState(i, Follower)
                 /\ SetVotedFor(i, Nil)
                 /\ UNCHANGED<<  candidateVars, logVars, leaderVars >>
                 /\ NetUpdate2(NetDelMsg(m), 
                                    <<"HandleMsgRVR","demote-to-follower", j, i, m.seq>>)  
            ELSE IF /\ data.term = currentTerm[i]
                    /\ raftState[i] = Candidate
                 THEN   IF data.success
                        THEN  /\ \/ /\ data.voteGranted
                                    /\ votesGranted' = [votesGranted EXCEPT ![i] =
                                                        votesGranted[i] \cup {j}] 
                                  \/ /\ ~data.voteGranted
                                     /\ UNCHANGED <<votesGranted>>
                              /\ IF IsQuorum(votesGranted'[i]) 
                                 THEN /\ BecomeLeader(i)
                                      /\ NetUpdate2(NetDelMsg(m), 
                                            <<"HandleMsgRVR","pormote", j, i, m.seq>>)  
            \*                            /\ Assert(FALSE, <<"HandleMsgRVR: pormote">>)  
                                 ELSE /\ UNCHANGED << nextIndex, matchIndex, raftState>>
                                      /\ NetUpdate2(NetDelMsg(m), 
                                            <<"HandleMsgRVR","get vote", j, i, m.seq>>)
                              /\ UNCHANGED<< votedFor, logVars, currentTerm>>
                        ELSE /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRVR", "stale msg", j, i, m.seq>>)
                            /\ UNCHANGED<< noNetVars>>
                 ELSE /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRVR", "stale msg", j, i,m.seq>>)
                      /\ UNCHANGED<< noNetVars>>
       ELSE \* raftState[i] = Follower
            IF data.term > currentTerm[i]
            THEN /\ SetCurrentTerm(i, data.term)
                 /\ UNCHANGED<<  votedFor, raftState, candidateVars, logVars, leaderVars >>
                 /\ NetUpdate2(NetDelMsg(m), 
                                    <<"HandleMsgRVR","demote-follower-stay", j, i, m.seq>>)  
            ELSE /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgRVR", "stale msg", j, i,m.seq>>)
                 /\ UNCHANGED<< noNetVars>>
       
                     
    
\* changed currentTerm, state, votedFor
\* Since one function in tla will result in one state change, 
\* and validateterm in draftos is a decorator that will enter other functions after execution, 
\* which may result in two message transfers, this method cannot be used in tla
\*ValidateTerm(i, j, m) ==
\*    LET data == m.data
\*    IN  /\ IF  data.term > currentTerm[i]
\*            THEN /\ currentTerm'    = [currentTerm EXCEPT ![i] = data.term]
\*                /\ raftState'          = [raftState       EXCEPT ![i] = Follower]
\*                /\ votedFor'       = [votedFor    EXCEPT ![i] = Nil]
\*                \* messages is unchanged so m can be processed further.
\*                /\ UNCHANGED <<netVars>>
\*            ELSE IF /\ data.term < currentTerm[i]
\*                    /\ \/ m.type = RV
\*                       \/ m.type = AppendEntriesRequest
\*                 THEN LET   rb  == [ term |-> currentTerm'[i], success |-> FALSE ]
\*                            reply == [ type |-> IF m.type = RV 
\*                                                THEN RVR
\*                                                ELSE AER,
\*                                    src |-> i,
\*                                    dst |-> j,
\*                                    data |-> rb ]
\*                        IN  /\ UNCHANGED<<currentTerm, raftState, votedFor>>
\*                            /\ NetUpdate2(NetReplyMsg(reply, m), 
\*                                    <<"Validate stale message, reply false", j ,i>>)
\*                 ELSE UNCHANGED<<netVars, currentTerm, raftState, votedFor>>
\*         /\ UNCHANGED <<commitIndex, log, matchIndex, nextIndex, votesGranted>>

\* todo : 

\*  logOk == \/ data.prevLogIdx = 0
\*                      \/ /\ data.prevLogIdx > 0
\*                         /\ data.prevLogIdx <= Len(log[i])
\*                         /\ data.prevLogTerm = log[i][data.prevLogIdx].term

HandleMsgAE(i, j, m) == 
    /\ m.type = AE
    /\  LET data == m.data
            commitIdx == data.commitIndex
            afterDeleteLog == DeleteEntriesFrom(i, data.prevLogIdx)
            rb1 == [ term       |-> currentTerm'[i],
                     success    |-> FALSE]
            rb2 == [ term               |-> currentTerm'[i],
                     success            |-> TRUE,
                     last_log_index     |-> data.prevLogIdx + Len(data.entries) ]
            msg == [ type       |-> AER,
                     src       |-> i,
                     dst         |-> j ]  \* Body is not included here.
        IN  /\ data.term >= currentTerm[i]
            /\ IF data.term > currentTerm[i]  \* here, not use checkTermToFollowed because we also need use this in candidate and leader situation
               THEN /\ SetCurrentTerm(i, data.term)
               ELSE UNCHANGED <<currentTerm>>
            /\ IF raftState[i] /= Follower
               THEN /\ SetState(i, Follower)
                    /\ SetVotedFor(i, Nil)
                    /\ NetUpdate2(NetDelMsg(m), 
                           <<"HandleMsgAE", "candidate to follower", j, i, m.seq>>)  
                    /\ UNCHANGED <<leaderVars, candidateVars, logVars>>
               ELSE /\ UNCHANGED << votedFor, raftState, leaderVars, candidateVars>>
                    /\ IF \/ data.prevLogIdx > Len(log[i])
                          \/ /\ data.prevLogIdx /= 0
                             /\ log[i][data.prevLogIdx].term /= data.prevLogTerm
                       THEN LET reply          == msg @@ ("data" :> rb1)
                            IN /\ NetUpdate2(NetReplyMsg(reply, m), 
                                        <<"HandleMsgAE", "term-mismatch", j, i, m.seq>>)
                               /\ UNCHANGED logVars
                       ELSE LET dataNextIdx    == data.prevLogIdx + 1
                                reply          == msg @@ ("data" :> rb2)
                                entries        == data.entries
                            IN /\ IF /\ dataNextIdx <= Len(log[i])
                                     /\ Len(entries) /= 0
                                     /\ log[i][dataNextIdx].term /= entries[1].term  
                                  THEN /\ log' = [log EXCEPT ![i] = afterDeleteLog \o entries ] 
                                  ELSE IF /\ dataNextIdx <= Len(log[i])
                                          /\ Len(entries) /= 0
                                          /\ log[i][dataNextIdx].term = entries[1].term
                                       THEN UNCHANGED log
                                       ELSE log' = [log EXCEPT ![i] = log[i] \o entries ]
                               /\ NetUpdate2(NetReplyMsg(reply, m), 
                                        <<"HandleMsgAE", "success", j, i, m.seq>>)
                               /\ IF commitIdx > GetCommitIdx(i)
                                  THEN SetCommitIdx(i, Min(commitIdx, log'[i][Len(log'[i])].idx))
                                  ELSE UNCHANGED commitIndex 

CanCommitIdx(s, idx) ==
    LET c1 == /\ commitIndex[s] < idx 
              /\ log[s][idx].term = currentTerm[s]
        c2 == IsQuorum({i \in Servers \ {s} : matchIndex'[s][i] >= idx} \union {s})
    IN IF c1 /\ c2
       THEN TRUE
       ELSE FALSE 


\* AdvanceCommitIdx(s) ==
\*     LET commitIdx == commitIndex[s]
\*         len     == Len(log[s])
\*         F[j \in commitIdx ..len] ==
\*         IF j = commitIdx
\*         THEN <<commitIdx>>  \* canCommitIdx, flag
\*         ELSE LET k == CanCommitIdx(s, j)
\*              IN IF  k = TRUE
\*                 THEN <<j>>
\*                 ELSE <<F[j-1][1]>>     
\*     IN commitIndex' = [commitIndex EXCEPT ![s] = F[len][1]]

AdvanceCommitIdx(s) ==
    LET commitIdx == commitIndex[s]
        len     == Len(log[s])
        F[j \in commitIdx ..len] ==
        IF j = commitIdx
        THEN <<commitIdx, TRUE>>  \* canCommitIdx, flag
        ELSE LET k == CanCommitIdx(s, j)
             IN IF /\ k = TRUE
                   /\ F[j-1][2] = TRUE
                THEN <<j, TRUE>>
                ELSE <<F[j-1][1], FALSE>>
    IN commitIndex' = [commitIndex EXCEPT ![s] = F[len][1]]



HandleMsgAER(i, j, m) == 
    /\ m.type = AER
    /\ LET data == m.data
           demote == data.term > currentTerm[i]
       IN /\ data.term >= currentTerm[i]
          /\ IF demote
             THEN /\ CheckTermBecomeFollower(i, data.term)
                  /\ SetVotedFor(i, Nil)
                  /\ NetUpdate2(NetDelMsg(m), 
                                    <<"HandleMsgAER", "server-out-of-date", j, i, m.seq>>)
                  /\ UNCHANGED<<candidateVars, logVars, leaderVars >>
             ELSE /\ CheckStateIs(i, Leader)  
                  /\ IF data.success
                    \* here we need add last_log_index > matchIndex[i][j] , or matchindex may decrease ,it's raftos bug
                     THEN /\ IF data.last_log_index > matchIndex[i][j]
                             THEN /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = data.last_log_index + 1]
                                  /\ matchIndex' = [matchIndex EXCEPT ![i][j] = data.last_log_index]  
                             ELSE UNCHANGED << nextIndex, matchIndex>> 
                    \*  THEN /\ nextIndex'  = [nextIndex  EXCEPT ![i][j] = data.last_log_index + 1]    
                    \*       /\ matchIndex' = [matchIndex EXCEPT ![i][j] = data.last_log_index]  
                          /\ AdvanceCommitIdx(i)
                          /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgAER", 
                                "success", j, i, m.seq>>)
                     ELSE /\ IF nextIndex[i][j] > matchIndex[i][j] + 1 
                             THEN  nextIndex' = [nextIndex EXCEPT ![i][j] =
                                       Max(nextIndex[i][j] - 1, 1)]
                             ELSE UNCHANGED<<nextIndex>>
                          /\ UNCHANGED <<matchIndex, commitIndex>>
                          /\ NetUpdate2(NetDelMsg(m), <<"HandleMsgAER", 
                                 "fail", j, i, m.seq>>)
                  /\ UNCHANGED <<candidateVars, log, serverVars>>

HandleStaleMsg(m) ==
    LET data == m.data
        src == m.src
        dst == m.dst
        rb == [term |-> GetCurrentTerm(dst), 
                success |-> FALSE, 
                curIdx |-> -1]
        reply == [ type |-> IF m.type = RV 
                            THEN RVR
                            ELSE AER,
                   src |-> dst,
                   dst |-> src,
                   data |-> rb ]
    IN /\ GetCurrentTerm(dst) > data.term
       /\ NetUpdate2(NetReplyMsg(reply, m), <<"Drop stale message", src, dst, m.seq>>)
       /\ UNCHANGED <<noNetVars>>

ClientRequest(n, v) ==
    /\ CheckStateIs(n, Leader)
    /\ log' = [ log EXCEPT ![n] = LogAppendEntry(n, v) ]
    /\ UNCHANGED <<serverVars, matchIndex, nextIndex, candidateVars, commitIndex>>
    /\ LET toSend == GetAppendEntriesNoSend(n, nextIndex)
           m == toSend[1]
       IN NetUpdate2(NetmanIncField("n_op", NetBatchAddMsg(m)), <<"ClientRequest", n, v>>)


MessageDrop(m) ==
    LET seq == m.seq
    IN  NetUpdate2(NetmanIncField("n_drop", NetDropMsg(m)), <<"DropMessage", seq>>)

MessageDuplicate(m) ==
    LET seq == m.seq
    IN  NetUpdate2(NetmanIncField("n_dup", NetDupMsg(m)), <<"DupMessage", seq>>)


(***************************************************************************
  Invariants
 ***************************************************************************)

SelectSeqWithIdx(s, Test(_,_)) == 
    LET F[i \in 0..Len(s)] == 
        IF i = 0
        THEN <<>>
        ELSE IF Test(s[i], i)
             THEN Append(F[i-1], s[i])
             ELSE F[i-1]
    IN F[Len(s)]


LeaderAppendOnly ==
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
        THEN LET iLog == log'[i]
                 jLog == log'[j]
                 len == Min(Len(iLog), Len(jLog))
                 F[k \in 0..len] ==
                    IF k = 0 THEN <<>>
                    ELSE LET key1 == <<iLog[k].term, iLog[k].idx>>
                             value1 == iLog[k].cmd
                             key2 == <<jLog[k].term, jLog[k].idx>>
                             value2 == jLog[k].cmd
                             F1 == IF key1 \in DOMAIN F[k-1]
                                   THEN IF F[k-1][key1] = value1 THEN F[k-1] ELSE F[k-1] @@ (<< -1, -1>> :> << key1, value1, F[k-1][key1] >> )
                                   ELSE F[k-1] @@ (key1 :> value1)
                             F2 == IF key2 \in DOMAIN F1
                                   THEN IF F1[key2] = value2 THEN F1 ELSE F1 @@ ( << -1, -1>> :> <<key2, value2, F1[key2]>>)
                                   ELSE F1 @@ (key2 :> value2)
                         IN F2
             IN << -1, -1>> \notin DOMAIN F[len]
        ELSE TRUE  
        
        
LeaderCommitCurrentTermLogs ==
    \A i \in Servers:
        IF raftState'[i] = Leader
        THEN IF commitIndex[i] /= commitIndex'[i]
             THEN log'[i][commitIndex'[i]].term = currentTerm'[i]
             ELSE TRUE
        ELSE TRUE       
                                   
                                   
ElectionSafety ==
    LET TwoLeader ==
            \E i, j \in Servers:
                /\ i /= j
                /\ currentTerm'[i] = currentTerm'[j]
                /\ raftState'[i] = Leader
                /\ raftState'[j] = Leader
    IN ~TwoLeader

MonotonicCurrentTerm == \A i \in Servers: currentTerm' [i] >= currentTerm[i]

MonotonicCommitIdx == \A i \in Servers: commitIndex'[i] >= commitIndex[i]

MonotonicMatchIdx ==
    \A i \in Servers:
        IF raftState'[i] = Leader /\ raftState[i] = Leader
        THEN \A j \in Servers:  matchIndex'[i][j] >= matchIndex[i][j]
        ELSE TRUE

NextIdxGtMatchIdx ==
    \A i \in Servers:
        IF raftState'[i] = Leader
        THEN \A j \in Servers: nextIndex'[i][j] > matchIndex'[i][j]
        ELSE TRUE

NextIdxGtZero ==
    \A i \in Servers:
        IF raftState'[i] = Leader
        THEN \A j \in Servers: nextIndex'[i][j] > 0
        ELSE TRUE
        
CommitIdxLELogLen ==
    \A i \in Servers: 
        IF Len(log'[i]) > 0
        THEN commitIndex'[i] <= log'[i][Len(log'[i])].idx
        ELSE TRUE




CommitProgress ==
    \A me \in Servers:  
        IF raftState'[me] /= Leader \/ matchIndex' = matchIndex  
        THEN TRUE
        ELSE LET nServer == Cardinality(Servers)
                 F[i \in 0..nServer - 1] ==        
                    IF i = 0 THEN <<<<>>, Servers \ {me}>>                                                                                                 
                    ELSE LET n == CHOOSE n \in F[i-1][2]: TRUE      
                         IN <<Append(F[i-1][1], matchIndex'[me][n]), F[i-1][2] \ {n}>>     
                 sorted_match_idx == SortSeq(F[nServer - 1][1], LAMBDA x, y: x >  y)     
                 commit == sorted_match_idx[nServer \div 2 ]      
            IN  IF GetPrevLogTerm(log'[me], commit) = currentTerm'[me] 
                THEN commit = commitIndex'[me]
                    \*  /\ PrintT(commit)
                ELSE TRUE
                
                   
                 

CommittedLogDurable ==
    \A i \in Servers:
        LET len     == Min(commitIndex'[i], commitIndex[i])
            logNext == SubSeq(log'[i], 1, len)
            logCur  == SubSeq(log[i], 1, len)
        IN IF len = 1 THEN TRUE
           ELSE /\ Len(logNext) >= len
                /\ Len(logCur) >= len
                /\ logNext = logCur

CommittedLogReplicatedMajority ==
     \A i \in Servers:
        IF raftState'[i] /= Leader 
        THEN TRUE
        ELSE LET entries == SubSeq(log'[i], 1, commitIndex'[i])
                 len     == Len(entries)
                 nServer == Cardinality(Servers)
                 F[j \in 0..nServer] ==
                    IF j = 0
                    THEN <<{}, {}>>
                    ELSE LET k == CHOOSE k \in Servers: k \notin F[j-1][1]
                             logLenOk == Len(log'[k]) >= commitIndex'[i]
                             kEntries == SubSeq(log'[k], 1, commitIndex'[i])
                         IN IF /\ logLenOk
                               /\ entries = kEntries
                             THEN <<F[j-1][1] \union {k}, F[j-1][2] \union {k}>>
                             ELSE <<F[j-1][1] \union {k}, F[j-1][2]>>
             IN IsQuorum(F[nServer][2])

InvSequence == <<
    ElectionSafety,
    LeaderAppendOnly,
    LogMatching,
    MonotonicCurrentTerm,
    \* MonotonicCommitIdx,
    MonotonicMatchIdx,
    CommittedLogDurable,
    CommittedLogReplicatedMajority,
    NextIdxGtMatchIdx,
    NextIdxGtZero,
\*\*     FollowerLogLELeaderLogAfterAE,
    CommitIdxLELogLen,
    CommitProgress,
    LeaderCommitCurrentTermLogs
    
>>

INV == Len(SelectSeqWithIdx(inv, LAMBDA x, y: ~x /\ y \notin netman.no_inv)) = 0
 (***************************************************************************
  Next actions
 ***************************************************************************)
DoHandleMsgRV ==
    /\ \E m \in msgs : 
        /\ m.type = RV
        /\ \/ HandleStaleMsg(m)
           \/ HandleMsgRV(m.dst, m.src, m)
    /\ inv' = InvSequence
            

DoHandleMsgRVR ==
    /\ \E m \in msgs : 
        /\ m.type = RVR
        /\ HandleMsgRVR(m.dst, m.src,  m)
    /\ inv' = InvSequence

DoHandleMsgAE ==
    /\ \E m \in msgs : 
        /\ m.type = AE
        /\ \/ HandleStaleMsg(m)
           \/ HandleMsgAE(m.dst, m.src,  m)
    /\ inv' = InvSequence

DoHandleMsgAER ==
    /\ \E m \in msgs : 
        /\ m.type = AER
        /\ HandleMsgAER(m.dst, m.src,  m)
    /\ inv' = InvSequence


DoRestart == 
    /\ PrePrune(netman.n_restart, "MaxRestartTimes")
    /\ \E n \in Servers : Restart(n)
    /\ inv' = InvSequence

DoElectionTimeout ==
    /\ PrePrune(netman.n_elec, "MaxElectionTimes")
    /\ \E n \in Servers: CheckStateIs(n, Follower) /\ TimeOut(n)
    /\ inv' = InvSequence

DoClientRequest ==
    /\ PrePrune(netman.n_op, "MaxClientOperationsTimes")
    /\ \E n \in Servers, v \in Commands:
        ClientRequest(n, v)
    /\ inv' = InvSequence

DoSendAppendEntries ==
    /\ PrePrune(netman.n_ae,   "MaxAppenEntriesTimes")
    /\ \E n \in Servers: /\ CheckStateIs(n, Leader)
                         /\ UNCHANGED <<serverVars, matchIndex, nextIndex, candidateVars, logVars>>
                         /\ SendAppendEntries(n)
    /\ inv' = InvSequence


DoMessageDrop == 
    /\ PrePrune(netman.n_drop,   "MaxDrop")
    /\ \E m \in msgs :  /\ UNCHANGED <<noNetVars>>
                        /\ MessageDrop(m)
    /\ inv' = InvSequence

DoMessageDuplicate == 
    /\ PrePrune(netman.n_dup,   "MaxDuplicate")
    /\ \E m \in msgs : /\ UNCHANGED <<noNetVars>>
                       /\ MessageDuplicate(m)
    /\ inv' = InvSequence

Next == 
\*    \/ DoRestart
    \/ DoElectionTimeout
    \/ DoSendAppendEntries
    \/ DoHandleMsgRV
    \/ DoHandleMsgRVR
    \/ DoHandleMsgAE
    \/ DoHandleMsgAER
    \/ DoMessageDrop
    \/ DoMessageDuplicate 
    \/ DoClientRequest 

Spec == Init /\ [][Next]_vars


====


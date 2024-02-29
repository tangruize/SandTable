---------------------------- MODULE XRaftPrevote ----------------------------
(***************************************************************************)
(* Source code: NodeImpl.java                                              *)
(***************************************************************************)

EXTENDS Sequences, Naturals, Integers, FiniteSets, TLC, SequencesExt

(***************************************************************************)
(* Constants definitions                                                   *)
(***************************************************************************)
CONSTANTS Servers  \* set of servers
CONSTANTS Follower, Candidate, Leader  \* server states
CONSTANTS Commands, NoOp  \* commands of normal log entries
CONSTANTS M_PV, M_PVR, M_RV, M_RVR, M_AE, M_AER  \* basic raft msg types + prevote
CONSTANTS Nil  \* a placeholder

(***************************************************************************)
(* Variables definitions                                                   *)
(***************************************************************************)
VARIABLES current_term, voted_for, log  \* persistent vars
VARIABLES commit_idx, state  \* volatile vars
VARIABLES next_idx, match_idx  \* leader vars
VARIABLES votes_count  \* candidate vars
VARIABLES leader_id  \* node vars
VARIABLES last_msg_id  \* to store last ae id, only used by leader

(***************************************************************************)
(* Network variables and instance                                          *)
(***************************************************************************)
VARIABLES netman, netcmd, msgs
INSTANCE FifoNetwork WITH FLUSH_DISCONN <- TRUE, NULL_MSG <- Nil,
    _msgs <- msgs, _netman <- netman, _netcmd <- netcmd

(***************************************************************************)
(* Self manipulated invariants checking                                    *)
(***************************************************************************)
VARIABLES inv

(***************************************************************************)
(* Vars groups                                                             *)
(***************************************************************************)
serverVars    == <<current_term, voted_for, state>>
leaderVars    == <<next_idx, match_idx, last_msg_id>>
candidateVars == <<votes_count>>
logVars       == <<log, commit_idx>>
nodeVars      == <<leader_id>>
netVars       == <<netman, netcmd, msgs>>
noNetVars     == <<serverVars, leaderVars, candidateVars, logVars, nodeVars>>
vars          == <<noNetVars, netVars, inv>>

(***************************************************************************)
(* State constraints helper                                                *)
(***************************************************************************)
CONSTANTS Parameters  \* to control the model scale

GetParameterSet(p)  == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE {}

CheckParameterHelper(n, p, Test(_,_)) ==
    IF p \in DOMAIN Parameters
    THEN Test(n, Parameters[p])
    ELSE TRUE
CheckParameterMax(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i <= j)

PrePrune(n, p) == CheckParameterHelper(n, p, LAMBDA i, j: i < j)

(***************************************************************************)
(* Type Ok                                                                 *)
(***************************************************************************)
TypeOkServerVars ==
    /\ current_term \in [ Servers -> Nat ]
    /\ voted_for    \in [ Servers -> Servers \cup {Nil} ]
    /\ state        \in [ Servers -> { Follower, Candidate, Leader } ]
TypeOkLeaderVars ==
    /\ next_idx     \in [ Servers -> [ Servers -> Nat \ {0} ]]
    /\ match_idx    \in [ Servers -> [ Servers -> Nat ]]
    /\ last_msg_id  \in [ Servers -> [ Servers -> Nat ]]
TypeOkCandidateVars ==
    /\ votes_count  \in [ Servers -> Nat ]
TypeOkLogVars ==
    \* log data structure is complex, we skip checking it
    /\ commit_idx   \in [ Servers -> Nat ]
TypeOkNodeVars ==
    /\ leader_id    \in [ Servers -> Servers \cup {Nil} ]
TypeOk ==
    /\ TypeOkServerVars
    /\ TypeOkLeaderVars
    /\ TypeOkCandidateVars
    /\ TypeOkLogVars
    /\ TypeOkNodeVars

(***************************************************************************)
(* Init variables                                                          *)
(***************************************************************************)
InitServerVars ==
    /\ current_term = [ i \in Servers |-> 0 ]
    /\ voted_for    = [ i \in Servers |-> Nil ]
    /\ state        = [ i \in Servers |-> Follower ]
InitLeaderVars ==
    /\ next_idx     = [ i \in Servers |-> [ j \in Servers |-> 1 ]]
    /\ match_idx    = [ i \in Servers |-> [ j \in Servers |-> 0 ]]
    /\ last_msg_id  = [ i \in Servers |-> [ j \in Servers |-> 0 ]]
InitCandidateVars ==
    /\ votes_count  = [ i \in Servers |-> 0 ]
InitLogVars ==
    /\ log = [ i \in Servers |-> <<>> ]
    /\ commit_idx   = [ i \in Servers |-> 0 ]
InitNodeVars ==
    /\ leader_id    = [ i \in Servers |-> Nil ]
InitNetVars ==
    /\ InitFifoNetworkAddNetman(Servers, <<"Init", Cardinality(Servers)>>, 
            [ n_op |-> 0, n_ae |-> 0, n_elec |-> 0, no_inv |-> GetParameterSet("NoInv")])
InitInv ==
    /\ inv = <<>>

Init ==
    /\ InitServerVars
    /\ InitLeaderVars
    /\ InitCandidateVars
    /\ InitLogVars
    /\ InitNodeVars
    /\ InitNetVars
    /\ InitInv

(***************************************************************************)
(* Helper functions                                                        *)
(***************************************************************************)
NumServer == Cardinality(Servers)
Max(a, b) == IF a > b THEN a ELSE b
Min(a, b) == IF a < b THEN a ELSE b
IsQuorum(ss) == Cardinality(ss) * 2 > NumServer
IsQuorumNum(num) == num * 2 > NumServer
Update(var, n, value) == [ var EXCEPT ![n] = value ]
UpdateCurrentTerm(n, term) == current_term' = Update(current_term, n, term)
UpdateVotedFor(n, node) == voted_for' = Update(voted_for, n, node)
UpdateState(n, s) == state' = Update(state, n, s)
UpdateLeaderId(n, id) == leader_id' = Update(leader_id, n, id)
AddVotes(me, node) == votes_count' = [ votes_count EXCEPT ![me] = @ + 1 ]
ClearVotes(me) == votes_count' = [ votes_count EXCEPT ![me] = 1 ]
UpdateMatchIdx(me, node, idx) == match_idx' = [ match_idx EXCEPT ![me][node] = idx ]
UpdateNextIdx(me, node, idx) == next_idx' = [ next_idx EXCEPT ![me][node] = IF idx < 1 THEN 1 ELSE idx ]
UpdateCommitIdx(n, idx) == commit_idx' = Update(commit_idx, n, idx)
IncLastMsgIdAll(n) == last_msg_id' = [ last_msg_id EXCEPT ![n] = [ i \in DOMAIN @ |-> @[i] + 1 ] ]
IncLastMsgIdSingle(me, node) == last_msg_id' = [ last_msg_id EXCEPT ![me][node] = @ + 1 ]

(***************************************************************************)
(* Log helpers                                                             *)
(***************************************************************************)
\* Currently, the log won't be compacted
LogAppend(log_, entry) == Append(log_, entry)
LogCount(log_) == Len(log_)
LogGetEntry(log_, idx) ==
    IF idx > LogCount(log_) \/ idx <= 0 THEN Nil ELSE log_[idx]
LogGetEntriesFrom(log_, idx) ==
    IF idx > LogCount(log_) \/ idx <= 0 THEN <<>>
    ELSE SubSeq(log_, idx, LogCount(log_))
LogGetEntriesTo(log_, idx) ==
    IF Len(log_) < idx THEN log_
    ELSE SubSeq(log_, 1, idx)
LogDeleteEntriesFrom(log_, idx) == SubSeq(log_, 1, idx - 1)
LogCurrentIdx(log_) == LogCount(log_)
LogLastTerm(log_) ==
    LET idx == LogCount(log_)
        term == IF idx = 0 THEN 0 ELSE log_[idx].term
    IN term
LogGetTerm(log_, idx) ==
    IF LogCount(log_) < idx
    THEN Assert(FALSE, <<"no such log entry", log_, idx>>)
    ELSE IF idx = 0 THEN 0 ELSE log_[idx].term
LogGetMatchEntries(log_, entries, prevLogIdx) ==
    LET F[i \in 0..Len(entries)] ==
            IF i = 0 THEN Nil
            ELSE LET ety1 == LogGetEntry(log_, prevLogIdx + i)
                     ety2 == LogGetEntry(entries, i)
                     entries1 == LogGetEntriesTo(log_, prevLogIdx + i - 1)
                     entries2 == LogGetEntriesFrom(entries, i)
                 IN IF /\ F[i-1] = Nil
                       /\ \/ ety1 = Nil
                          \/ ety1.term /= ety2.term
                    THEN entries1 \o entries2
                    ELSE F[i-1]
        result == F[Len(entries)]
    IN IF result = Nil THEN log_ ELSE result

(***************************************************************************)
(* Msg constructors                                                        *)
(***************************************************************************)
_BatchExcludesReqMsgsArg(n, excludes, Constructor2(_, _), Constructor3(_, _, _), arg) ==
    LET dsts == Servers \ excludes
        size == Cardinality(dsts)
        F[i \in 0..size] ==
            IF i = 0 THEN <<<<>>, dsts>>
            ELSE LET ms == F[i-1][1]
                     s == CHOOSE j \in F[i-1][2]: TRUE
                     m == IF arg = Nil
                          THEN Constructor2(n, s)
                          ELSE Constructor3(n, s, arg)
                     remaining == F[i-1][2] \ {s}
                 IN <<Append(ms, m), remaining>>
    IN F[size][1]

_Dummy2(a, b) == TRUE
_Dummy3(a, b, c) == TRUE

BatchReqMsgs(n, Constructor(_, _)) ==
    _BatchExcludesReqMsgsArg(n, {n}, Constructor, _Dummy3, Nil)
BatchReqMsgsArg(n, Constructor(_, _, _), arg) ==
    _BatchExcludesReqMsgsArg(n, {n}, _Dummy2, Constructor, arg)

ConstructMsg(src, dst, type, body) ==
    [ src |-> src, dst |-> dst, type |-> type, body |-> body ]

PreVote(i, j) ==  \* doProcessElectionTimeout
    LET body == [ term |-> current_term'[i],
                  last_log_idx |-> LogCurrentIdx(log[i]),
                  last_log_term |-> LogLastTerm(log[i]) ]
    IN ConstructMsg(i, j, M_PV, body)

PreVoteResponse(m) ==  \* func: doProcessPreVoteResult
    LET i == m.dst
        j == m.src
        req == m.body
        meTerm == current_term'[i]
        meLastTerm == LogLastTerm(log[i])
        grantMeLogOlder == \/ meLastTerm < req.last_log_term
                           \/ /\ req.last_log_term = meLastTerm
                              /\ LogCurrentIdx(log[i]) <= req.last_log_idx
        body == [ term |-> meTerm,
                  vote_granted |-> grantMeLogOlder ]
    IN ConstructMsg(i, j, M_PVR, body)

RequestVote(i, j) ==  \* startElection
    LET body == [ term |-> current_term'[i],
                  candidate_id |-> i,
                  last_log_idx |-> LogCurrentIdx(log[i]),
                  last_log_term |-> LogLastTerm(log[i]) ]
    IN ConstructMsg(i, j, M_RV, body)

RequestVoteResponse(m, voted) ==  \* func: doProcessRequestVoteRpc
    LET i == m.dst
        j == m.src
        req == m.body
        meTerm == current_term'[i]
        rejectMeTermIsBigger == meTerm > req.term
        rejectVotedForSelf == /\ meTerm = req.term
                              /\ state'[i] \in {Candidate, Leader}
        meLastTerm == LogLastTerm(log[i])
        _rejectMeLogNewer == ~(\/ meLastTerm < req.last_log_term
                              \/ /\ req.last_log_term = meLastTerm
                                 /\ LogCurrentIdx(log[i]) <= req.last_log_idx)
        rejectStepDownMeLogNewer == /\ current_term[i] < req.term
                                    /\ _rejectMeLogNewer
        acceptVotedForCandidate == voted = j
        rejectVotedOtherOrMeLogNewer == /\ ~acceptVotedForCandidate
                                        /\ meTerm = req.term
                                        /\ \/ voted /= Nil
                                           \/ _rejectMeLogNewer
        voteStatus == IF rejectMeTermIsBigger         THEN "not-vote: term bigger"         ELSE
                      IF rejectStepDownMeLogNewer     THEN "not-vote: step down log newer" ELSE
                      IF rejectVotedForSelf           THEN "not-vote: voted for self"      ELSE
                      IF rejectVotedOtherOrMeLogNewer THEN "not-vote: voted or log newer"  ELSE "voted"
        granted == voteStatus = "voted"
        body == [ term |-> meTerm,
                  vote_granted |-> granted ]
    IN ConstructMsg(i, j, M_RVR, body) @@ [ status |-> voteStatus ]

\* TODO: set leader_id, message_id in msg
AppendEntriesNext(i, j, next) ==  \* func: AbstractLog.createAppendEntriesRpc
    LET prev_log_idx == next[i][j] - 1
        body == [ term |-> current_term[i],
                  msg_id |-> last_msg_id[i][j] + 1,
                  leader_commit |-> commit_idx'[i],
                  prev_log_idx |-> prev_log_idx,
                  prev_log_term |-> LogGetTerm(log'[i], prev_log_idx),
                  entries |-> LogGetEntriesFrom(log'[i], next[i][j]) ]
    IN ConstructMsg(i, j, M_AE, body)

AppendEntries(i, j) == AppendEntriesNext(i, j, next_idx)

AppendEntriesResponseFail(m) ==  \* func: AppendEntriesResult
    LET body == [ success |-> FALSE,
                  msg_id |-> m.body.msg_id,
                  term |-> Max(current_term[m.dst], m.body.term) ]
    IN ConstructMsg(m.dst, m.src, M_AER, body)

AppendEntriesResponseSuccess(m) ==  \* func: AppendEntriesResult
    LET req == m.body
        body == [ success |-> TRUE,
                  msg_id |-> m.body.msg_id,
                  last_entry_idx |-> req.prev_log_idx + Len(m.body.entries),  \* used: rpc.getLastEntryIndex()
                  term |-> Max(current_term[m.dst], req.term) ]
    IN ConstructMsg(m.dst, m.src, M_AER, body)


(***************************************************************************)
(* Raft actions                                                            *)
(***************************************************************************)

(***************************************************************************)
(* Election Timeout                                                        *)
(***************************************************************************)

StartElection(i, term) ==  \* startElection
    /\ UpdateState(i, Candidate)
    /\ UpdateCurrentTerm(i, term)
    /\ UpdateLeaderId(i, Nil)  \* CandidateNodeRole.getLeaderId
    /\ ClearVotes(i)
    /\ UNCHANGED <<voted_for, leaderVars, logVars>>
    /\ LET ms == BatchReqMsgs(i, RequestVote)
       IN NetUpdate2(NetBatchAddMsg(ms), <<"StartElection", i, term>>)

ElectionTimeout(i) ==  \* func: electionTimeout
    IF state[i] = Leader    THEN FALSE ELSE
    IF state[i] = Candidate THEN StartElection(i, current_term[i])
    ELSE  \* Follower
        /\ UNCHANGED <<state, current_term, leader_id>>
        /\ ClearVotes(i)
        /\ UNCHANGED <<voted_for, leaderVars, logVars>>
        /\ LET ms == BatchReqMsgs(i, PreVote)
           IN NetUpdate2(NetmanIncField("n_elec", NetBatchAddMsg(ms)), <<"ElectionTimeout", i>>)

(***************************************************************************)
(* Recv prevote                                                            *)
(***************************************************************************)

RecvPreVote(m) ==  \* func: doProcessPreVoteRpc
    LET req == m.body
        src == m.src
        dst == m.dst
        msg == PreVoteResponse(m)
    IN /\ UNCHANGED noNetVars
       /\ NetUpdate2(NetReplyMsg(msg, m), 
            <<"RecvPreVote", IF msg.body.vote_granted THEN "granted" ELSE "not granted", dst, src>>)

(***************************************************************************)
(* Recv prevote response                                               *)
(***************************************************************************)

RecvPreVoteResponse(m) ==  \* func: doProcessPreVoteResult
    LET resp == m.body
        src == m.src
        dst == m.dst
    IN  IF state[dst] /= Follower
        THEN /\ UNCHANGED noNetVars
             /\ NetUpdate2(NetDelMsg(m), <<"RecvPreVoteResponse", "not follower", dst, src>>)
        ELSE IF resp.vote_granted
             THEN IF IsQuorumNum(votes_count[dst] + 1)
                  THEN StartElection(dst, current_term[dst] + 1)
                  ELSE /\ AddVotes(dst, src)
                       /\ UNCHANGED <<serverVars, leaderVars, logVars, nodeVars>>
                       /\ NetUpdate2(NetDelMsg(m), <<"RecvPreVoteResponse", "granted", dst, src>>)
             ELSE /\ UNCHANGED noNetVars
                  /\ NetUpdate2(NetDelMsg(m), <<"RecvPreVoteResponse", "not granted", dst, src>>)


(***************************************************************************)
(* Recv requestvote                                                        *)
(***************************************************************************)

RecvRequestVote(m) ==  \* func: doProcessRequestVoteRpc
    LET req == m.body
        src == m.src
        dst == m.dst
        demote == current_term[dst] < req.term
        msg == RequestVoteResponse(m, IF demote THEN Nil ELSE voted_for[dst])
    IN /\ IF demote
          THEN /\ UpdateCurrentTerm(dst, req.term)
               /\ UpdateState(dst, Follower)
          ELSE UNCHANGED <<current_term, state>>
       /\ IF msg.body.vote_granted
          THEN /\ UpdateLeaderId(dst, Nil)
               /\ UpdateVotedFor(dst, src)
          ELSE IF demote
               THEN /\ UpdateLeaderId(dst, Nil)
                    /\ UpdateVotedFor(dst, Nil)
               ELSE UNCHANGED <<leader_id, voted_for>>
       /\ UNCHANGED <<leaderVars, candidateVars, logVars>>
       /\ NetUpdate2(NetReplyMsg(msg, m), 
            <<"RecvRequestVote", msg.status, dst, src>>)

(***************************************************************************)
(* Recv requestvote response                                               *)
(***************************************************************************)

BecomeFollower(i, term) ==  
    /\ UpdateCurrentTerm(i, term)
    /\ UpdateVotedFor(i, Nil)
    /\ UpdateState(i, Follower)
    /\ UpdateLeaderId(i, Nil)

BecomeLeader(i, m) ==  \* func: LeaderNodeRole
    /\ LET noop == [ term |-> current_term[i], data |-> Nil ]  \* doProcessRequestVoteResult
       IN log' = Update(log, i, LogAppend(log[i], noop))
    /\ UpdateState(i, Leader)
    /\ UpdateLeaderId(i, i)
    /\ match_idx' = [ match_idx EXCEPT ![i] = [ j \in Servers |-> 0 ] ]
    /\ next_idx' = [ next_idx EXCEPT ![i] = ( i :> 1 ) @@ [ j \in Servers |-> LogCurrentIdx(log[i]) + 1 ] ]

RecvRequestVoteResponse(m) ==  \* func: doProcessRequestVoteResult
    LET resp == m.body
        src == m.src
        dst == m.dst
    IN IF resp.term > current_term[dst]
       THEN /\ UNCHANGED <<leaderVars, candidateVars, logVars>>
            /\ BecomeFollower(dst, resp.term)
            /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "term is smaller", dst, src>>)
       ELSE IF state[dst] /= Candidate \/ resp.term /= current_term[dst]
            THEN /\ UNCHANGED noNetVars
                 /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "not candidate or term mismatch", dst, src>>)
            ELSE IF resp.vote_granted
                 THEN /\ AddVotes(dst, src)
                      /\ IF IsQuorumNum(votes_count'[dst])
                         THEN /\ UNCHANGED <<current_term, voted_for, commit_idx, last_msg_id>>
                              /\ BecomeLeader(dst, m)
                              /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "become leader", dst, src>>)
                         ELSE /\ UNCHANGED <<serverVars, leaderVars, logVars, nodeVars>>
                              /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "granted", dst, src>>)
                 ELSE /\ UNCHANGED noNetVars
                      /\ NetUpdate2(NetDelMsg(m), <<"RecvRequestVoteResponse", "not granted", dst, src>>)

(***************************************************************************)
(* Send appendentries to all other nodes                                   *)
(***************************************************************************)
SendAppendentriesAll(n) ==  \* func: doReplicateLog
    /\ UNCHANGED <<logVars, serverVars, candidateVars, nodeVars, next_idx, match_idx>>
    /\ LET ms == BatchReqMsgsArg(n, AppendEntriesNext, next_idx)
       IN NetUpdate2(NetmanIncField("n_ae", NetBatchAddMsg(ms)), <<"SendAppendentriesAll", n>>)
    /\ IncLastMsgIdAll(n)

(***************************************************************************)
(* Recv appendentries                                                      *)
(***************************************************************************)
AcceptLeader(me, leader) ==
    /\ UpdateState(me, Follower)
    /\ UpdateLeaderId(me, leader)

SetCommitIdx(n, idx) ==
    /\ Assert(commit_idx[n] <= idx, "SetCommitIdx: commit_idx[n] <= idx")
    /\ Assert(idx <= LogCurrentIdx(log'[n]), <<"SetCommitIdx: idx <= LogCurrentIdx(log'[n])", n, idx, log'>>)
    /\ UpdateCommitIdx(n, idx)

RecvAppendentries(m) ==  \* func: doProcessAppendEntriesRpc
    LET req == m.body
        src == m.src
        dst == m.dst
        fail == AppendEntriesResponseFail(m)
        success == AppendEntriesResponseSuccess(m)
    IN IF req.term < current_term[dst]
       THEN /\ UNCHANGED noNetVars
            /\ NetUpdate2(NetReplyMsg(fail, m), <<"RecvAppendentries", "term is bigger", dst, src>>)
       ELSE /\ IF req.term > current_term[dst]
               THEN /\ UpdateCurrentTerm(dst, req.term)
                    /\ UpdateVotedFor(dst, Nil)
               ELSE UNCHANGED <<current_term, voted_for>>
            /\ AcceptLeader(dst, src)
            /\ LET prevLogIsLastSnapshot == req.prev_log_idx = 0  \* snapshot is not implemented, 0 is lastIncludedIndex
                   ety == LogGetEntry(log[dst], req.prev_log_idx)
                   noPrevLog == ety = Nil
                   termMismatch == ety.term /= req.prev_log_term
               IN IF /\ ~prevLogIsLastSnapshot
                     /\ \/ noPrevLog
                        \/ termMismatch
                  THEN IF noPrevLog
                       THEN /\ UNCHANGED <<leaderVars, candidateVars, logVars>>
                            /\ NetUpdate2(NetReplyMsg(fail, m), <<"RecvAppendentries", "no prev log", dst, src>>)
                       ELSE \* term mismatch, did not erase.
                            /\ UNCHANGED <<leaderVars, candidateVars, logVars>>
                            /\ NetUpdate2(NetReplyMsg(fail, m), <<"RecvAppendentries", "term mismatch", dst, src>>)
                  ELSE \* success
                       /\ UNCHANGED <<leaderVars, candidateVars>>
                       /\ log' = Update(log, dst, LogGetMatchEntries(log[dst], req.entries, req.prev_log_idx))
                       /\ IF commit_idx[dst] < req.leader_commit
                          THEN LET idxToCommit == Min(LogCurrentIdx(log'[dst]), req.leader_commit)
                               IN SetCommitIdx(dst, idxToCommit)
                          ELSE UNCHANGED commit_idx
                       /\ NetUpdate2(NetReplyMsg(success, m), <<"RecvAppendentries", "success", dst, src>>)

(***************************************************************************)
(* Recv appendentries response                                             *)
(***************************************************************************)
AdvanceCommitIdx(me) ==
    LET F[i \in 0..NumServer] ==
            IF i = 0 THEN <<<<>>, Servers>>
            ELSE LET n == CHOOSE n \in F[i-1][2]: TRUE
                 IN <<Append(F[i-1][1], match_idx'[me][n]), F[i-1][2] \ {n}>>
        sorted_match_idx == SortSeq(F[NumServer][1], LAMBDA x, y: x > y)
        commit == sorted_match_idx[NumServer \div 2 + 1]
        commit_ety == LogGetEntry(log[me], commit)
    IN IF commit_ety /= Nil /\ commit_ety.term = current_term[me]
       THEN SetCommitIdx(me, commit)
       ELSE UNCHANGED commit_idx

RecvAppendentriesResponse(m) ==  \* func: doProcessAppendEntriesResult
    LET resp == m.body
        src == m.src
        dst == m.dst
        failReason ==
            IF last_msg_id[dst][src] /= resp.msg_id THEN "stale msg" ELSE  \* AbstractHandler.channelRead
            IF resp.term > current_term[dst] THEN "term is smaller" ELSE
            IF state[dst] /= Leader THEN "not leader" ELSE
            IF ~resp.success THEN "fail retry" ELSE
            "success"
    IN IF failReason \in {"stale msg", "not leader"}
       THEN /\ UNCHANGED noNetVars
            /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", failReason, dst, src>>)
       ELSE IF failReason = "term is smaller"
            THEN /\ UNCHANGED <<leaderVars, candidateVars, logVars>>
                 /\ BecomeFollower(dst, resp.term)
                 /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", failReason, dst, src>>)
            ELSE IF failReason = "fail retry"
                 THEN LET next == next_idx[dst][src] - 1
                          nextForAe == [next_idx EXCEPT ![dst][src] = next]
                          retryAe == AppendEntriesNext(dst, src, nextForAe)
                      IN /\ UNCHANGED <<serverVars, match_idx, candidateVars, logVars, nodeVars>>
                         /\ next_idx' = nextForAe
                         /\ NetUpdate2(NetReplyMsg(retryAe, m), <<"RecvAppendentriesResponse", failReason, dst, src>>)
                         /\ IncLastMsgIdSingle(dst, src)
                 ELSE \* success
                      /\ Assert(resp.success, <<"RecvAppendentriesResponse", "assert success">>)
                      /\ UNCHANGED <<leader_id, log, serverVars, candidateVars>>
                      /\ UpdateMatchIdx(dst, src, resp.last_entry_idx)
                      /\ UpdateNextIdx(dst, src, resp.last_entry_idx + 1)
                      /\ IF \/ match_idx[dst][src] /= resp.last_entry_idx
                            \/ next_idx[dst][src] /= resp.last_entry_idx + 1
                         THEN AdvanceCommitIdx(dst)
                         ELSE UNCHANGED commit_idx
                      /\ IF next_idx'[dst][src] < LogCurrentIdx(log[dst])
                         THEN /\ NetUpdate2(NetReplyMsg(AppendEntriesNext(dst, src, next_idx'), m), <<"RecvAppendentriesResponse", "success retry", dst, src>>)
                              /\ IncLastMsgIdSingle(dst, src)
                         ELSE /\ NetUpdate2(NetDelMsg(m), <<"RecvAppendentriesResponse", "success", dst, src>>)
                              /\ UNCHANGED last_msg_id

(***************************************************************************)
(* Recv client entry on Leader                                             *)
(***************************************************************************)
RecvEntry(n, data) ==  \* func: appendLog
    /\ state[n] = Leader
    /\ UNCHANGED <<serverVars, candidateVars, nodeVars, commit_idx, next_idx, match_idx>>
    /\ LET ety == [ term |-> current_term[n], data |-> data ]
           ms == BatchReqMsgsArg(n, AppendEntriesNext, next_idx)
       IN /\ log' = Update(log, n, LogAppend(log[n], ety))
          /\ NetUpdate2(NetmanIncField("n_op", NetBatchAddMsg(ms)), <<"RecvEntry", n, data>>)
    /\ IncLastMsgIdAll(n)

(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
ElectionSafety ==
    LET TwoLeader ==
            \E i, j \in Servers:
                /\ i /= j
                /\ current_term'[i] = current_term'[j]
                /\ state'[i] = Leader
                /\ state'[j] = Leader
    IN ~TwoLeader

LeaderAppendOnly ==
    \A i \in Servers:
        IF state[i] = Leader /\ state'[i] = Leader
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
                    ELSE LET key1 == <<iLog[k].term, k>>
                             value1 == iLog[k].data
                             key2 == <<jLog[k].term, k>>
                             value2 == jLog[k].data
                             F1 == IF key1 \in DOMAIN F[k-1]
                                   THEN IF F[k-1][key1] = value1
                                        THEN F[k-1]
                                        ELSE F[k-1] @@ ( <<-1, -1>> :> <<key1, value1, F[k-1][key1]>> )
                                   ELSE F[k-1] @@ (key1 :> value1)
                             F2 == IF key2 \in DOMAIN F1
                                   THEN IF F1[key2] = value2
                                        THEN F1
                                        ELSE F1 @@ ( <<-1, -1>> :> <<key2, value2, F1[key2]>> )
                                   ELSE F1 @@ (key2 :> value2)
                         IN F2
             IN IF <<-1, -1>> \notin DOMAIN F[len] THEN TRUE
                ELSE Assert(FALSE, <<i, j, F>>)
        ELSE TRUE

MonotonicCurrentTerm == \A i \in Servers: current_term' [i] >= current_term[i]

MonotonicCommitIdx == \A i \in Servers: commit_idx'[i] >= commit_idx[i]

MonotonicMatchIdx ==
    \A i \in Servers:
        IF state[i] = Leader
        THEN \A j \in Servers:  match_idx'[i][j] >= match_idx[i][j]
        ELSE TRUE

CommittedLogDurable ==
    \A i \in Servers:
        LET len     == Min(commit_idx'[i], commit_idx[i])
            logNext == SubSeq(log'[i], 1, len)
            logCur  == SubSeq(log[i], 1, len)
        IN IF len = 1 THEN TRUE
           ELSE /\ Len(logNext) >= len
                /\ Len(logCur) >= len
                /\ logNext = logCur

CommittedLogReplicatedMajority ==
     \A i \in Servers:
        IF state'[i] /= Leader \/ commit_idx'[i] <= 1
        THEN TRUE
        ELSE LET entries == SubSeq(log'[i], 1, commit_idx'[i])
                 len     == Len(entries)
                 nServer == Cardinality(Servers)
                 F[j \in 0..nServer] ==
                    IF j = 0
                    THEN <<{}, {}>>
                    ELSE LET k == CHOOSE k \in Servers: k \notin F[j-1][1]
                             logLenOk == LogCount(log'[k]) >= commit_idx'[i]
                             kEntries == SubSeq(log'[k], 1, commit_idx'[i])
                         IN IF /\ logLenOk
                               /\ entries = kEntries
                             THEN <<F[j-1][1] \union {k}, F[j-1][2] \union {k}>>
                             ELSE <<F[j-1][1] \union {k}, F[j-1][2]>>
             IN IsQuorum(F[nServer][2])

NextIdxGtMatchIdx ==
    \A i \in Servers:
        IF state'[i] = Leader
        THEN \A j \in Servers \ {i}: next_idx'[i][j] > match_idx'[i][j]
        ELSE TRUE

NextIdxGtZero ==
    \A i \in Servers:
        IF state'[i] = Leader
        THEN \A j \in Servers: next_idx'[i][j] > 0
        ELSE TRUE

SelectSeqWithIdx(s, Test(_,_)) == 
    LET F[i \in 0..Len(s)] == 
        IF i = 0
        THEN <<>>
        ELSE IF Test(s[i], i)
             THEN Append(F[i-1], s[i])
             ELSE F[i-1]
    IN F[Len(s)]

FollowerLogLELeaderLogAfterAE ==
    LET cmd  == netcmd'[1]
        cmd1 == cmd[1]
        cmd2 == cmd[2]
        follower == cmd[3]
        leader   == cmd[4]
    IN IF cmd1 = "RecvAppendentries" /\ cmd2 \in { "success", "no prev log" }
       THEN IF log[follower] /= log'[follower]
            THEN LogCount(log'[follower]) <= LogCount(log'[leader])
            ELSE TRUE
       ELSE TRUE

CommitIdxLELogLen ==
    \A i \in Servers: commit_idx'[i] <= LogCount(log'[i])

LeaderCommitCurrentTermLogs ==
    \A i \in Servers:
        IF state'[i] = Leader
        THEN IF commit_idx[i] /= commit_idx'[i]
             THEN log'[i][commit_idx'[i]].term = current_term'[i]
             ELSE TRUE
        ELSE TRUE

NewLeaderTermNotInLog ==
    \A i \in Servers:
        IF state'[i] = Leader /\ state[i] /= Leader
        THEN \A j \in Servers \ {i}:
                \A n \in DOMAIN log'[j]:
                    log'[j][n].term /= current_term'[i]
        ELSE TRUE

LeaderTermLogHasGreatestIdx ==
    \A i \in Servers:
        IF state'[i] = Leader
        THEN \A j \in Servers \ {i}:
                LET IncTermLogCount(a, b) == IF a.term = current_term'[i] THEN b + 1 ELSE b
                IN FoldSeq(IncTermLogCount, 0, log'[i]) >= FoldSeq(IncTermLogCount, 0, log'[j])
        ELSE TRUE

InvSequence == <<
    ElectionSafety,
    LeaderAppendOnly,
    LogMatching,
    MonotonicCurrentTerm,
    MonotonicCommitIdx,
    MonotonicMatchIdx,
    CommittedLogDurable,
    CommittedLogReplicatedMajority,
    NextIdxGtMatchIdx,
    NextIdxGtZero,
    FollowerLogLELeaderLogAfterAE,
    CommitIdxLELogLen,
    LeaderCommitCurrentTermLogs,
    NewLeaderTermNotInLog,
    LeaderTermLogHasGreatestIdx
>>

INV == Len(SelectSeqWithIdx(inv, LAMBDA x, y: ~x /\ y \notin netman.no_inv)) = 0

(***************************************************************************)
(* State contraints                                                        *)
(***************************************************************************)

\*CONSTANTS MaxSentMsgs,
\*          MaxRecvMsgs,
\*          MaxWireMsgs,
\*          MaxPartitionTimes,
\*          MaxCureTimes,
\*          MaxClientOperationsTimes,
\*          MaxAppendEntriesTimes,
\*          MaxElectionTimes,
\*          MaxLogLength,
\*          MaxTerm

GetRealLogLen(curLog) == SelectSeq(curLog, LAMBDA i: i.data /= NoOp)
GetMaxLogLen == Len(log[CHOOSE i \in Servers: \A j \in Servers \ {i}:
                            GetRealLogLen(log[i]) >= GetRealLogLen(log[j])])
GetMaxTerm == current_term[CHOOSE i \in Servers: \A j \in Servers \ {i}:
                            current_term[i] >= current_term[j]]

ScSent == CheckParameterMax(netman.n_sent, "MaxSentMsgs")
ScRecv == CheckParameterMax(netman.n_recv, "MaxRecvMsgs")
ScWire == CheckParameterMax(netman.n_wire, "MaxWireMsgs")
ScLog  == CheckParameterMax(GetMaxLogLen,  "MaxLogLength")
ScTerm == CheckParameterMax(GetMaxTerm,    "MaxTerm")
ScPart == CheckParameterMax(netman.n_part, "MaxPartitionTimes")
ScCure == CheckParameterMax(netman.n_cure, "MaxCureTimes")
ScOp   == CheckParameterMax(netman.n_op,   "MaxClientOperationsTimes")
ScAe   == CheckParameterMax(netman.n_ae,   "MaxAppendEntriesTimes")
ScElec == CheckParameterMax(netman.n_elec, "MaxElectionTimes")

SC == /\ ScSent /\ ScRecv /\ ScWire /\ ScLog /\ ScTerm
      /\ ScPart /\ ScCure /\ ScOp   /\ ScAe  /\ ScElec

(***************************************************************************)
(* Next actions                                                            *)
(***************************************************************************)

_DoRecvM(type, func(_)) ==
    /\ \E src, dst \in Servers:
        /\ src /= dst
        /\ LET m == NetGetMsg(src, dst)
           IN /\ m /= Nil
              /\ m.type = type
              /\ func(m)
    /\ inv' = InvSequence

DoRecvPreVote == /\ _DoRecvM(M_PV, RecvPreVote)

DoRecvPreVoteResponse == /\ _DoRecvM(M_PVR, RecvPreVoteResponse)

DoRecvRequestVote == /\ _DoRecvM(M_RV, RecvRequestVote)

DoRecvRequestVoteResponse == /\ _DoRecvM(M_RVR, RecvRequestVoteResponse)

DoRecvAppendentries == /\ _DoRecvM(M_AE, RecvAppendentries)

DoRecvAppendentriesResponse == /\ _DoRecvM(M_AER, RecvAppendentriesResponse)

DoElectionTimeout ==
    /\ PrePrune(netman.n_elec, "MaxElectionTimes")
    /\ \E n \in Servers: ElectionTimeout(n)
    /\ inv' = InvSequence

DoRecvEntry ==
    /\ PrePrune(netman.n_op, "MaxClientOperationsTimes")
    /\ \E n \in Servers, v \in Commands: RecvEntry(n, v)
    /\ inv' = InvSequence

DoSendAppendentriesAll ==
    /\ PrePrune(netman.n_ae, "MaxAppendEntriesTimes")
    /\ \E n \in Servers:
        /\ state[n] = Leader
        /\ SendAppendentriesAll(n)
    /\ inv' = InvSequence

DoNetworkPartition ==
    /\ PrePrune(netman.n_part, "MaxPartitionTimes")
    /\ ~NetIsParted
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

Next ==
    \/ DoRecvPreVote
    \/ DoRecvPreVoteResponse
    \/ DoRecvRequestVote
    \/ DoRecvRequestVoteResponse
    \/ DoRecvAppendentries
    \/ DoRecvAppendentriesResponse
    \/ DoElectionTimeout
    \/ DoRecvEntry
    \/ DoSendAppendentriesAll
    \/ DoNetworkPartition
    \/ DoNetworkCure

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Mon May 01 23:27:32 CST 2023 by tangruize
\* Created Wed Apr 26 11:30:37 CST 2023 by tangruize

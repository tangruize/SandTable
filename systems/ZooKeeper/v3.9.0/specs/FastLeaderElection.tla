------------------------- MODULE FastLeaderElection -------------------------
\* This is the formal specification for Fast Leader Election in Zab protocol.
(* Reference:
   FastLeaderElection.java, Vote.java, QuorumPeer.java in https://github.com/apache/zookeeper.
   Medeiros A. ZooKeeper's atomic broadcast protocol: Theory and practice[J]. Aalto University School of Science, 2012. *)
EXTENDS Integers, FiniteSets, Sequences, Naturals, TLC, SequencesExt
-----------------------------------------------------------------------------
\* The set of server identifiers
CONSTANT Server

\* Server states
CONSTANTS LOOKING, FOLLOWING, LEADING, INITING
(* NOTE: In spec, we do not discuss servers whose ServerState is OBSERVING.*)

\* Message types
CONSTANTS NOTIFICATION

\* Timeout signal
CONSTANT NONE

\* Server order
CONSTANT ServerOrd

\* DisableInitBug1419, DisableBug1419
CONSTANT Parameters

-----------------------------------------------------------------------------
CheckParameterTrue(p) == IF p \in DOMAIN Parameters THEN Parameters[p] ELSE TRUE

Quorums == {Q \in SUBSET Server: Cardinality(Q)*2 > Cardinality(Server)}

NullPoint == CHOOSE p: p \notin Server

-----------------------------------------------------------------------------
\* Server's state(LOOKING, FOLLOWING, LEADING).
\* VARIABLE recorder
VARIABLE state

VARIABLE historyVotes

VARIABLE history

\* The epoch number of the last NEWLEADER packet accepted, used for comparing.
VARIABLE currentEpoch

\* The index and zxid of the last processed transaction in history.
VARIABLE lastProcessed

\* currentVote[i]: The server who i thinks is the current leader(id,zxid,peerEpoch,...).
VARIABLE currentVote

\* Election instance.(logicalClock in code)
VARIABLE logicalClock

\* The votes from the current leader election are stored in ReceiveVotes.
VARIABLE receiveVotes

(* The votes from previous leader elections, as well as the votes from the current leader election are
   stored in outofelection. Note that notifications in a LOOKING state are not stored in outofelection.
   Only FOLLOWING or LEADING notifications are stored in outofelection.  *)
VARIABLE outOfElection

\* recvQueue[i]: The queue of received notifications or timeout signals in server i.
VARIABLE recvQueue

\* A veriable to wait for new notifications, corresponding to line 1050 in FastLeaderElection.java.
VARIABLE waitNotmsg

\* leadingVoteSet[i]: The set of voters that follow i.
VARIABLE leadingVoteSet

(* The messages about election sent from one server to another.
   electionMsgs[i][j] means the input buffer of server j from server i. *)
VARIABLE electionMsgs
VARIABLE netcmd, recorder

net1 == INSTANCE FifoNetwork WITH FLUSH_DISCONN <- TRUE, NULL_MSG <- NONE,
        _msgs <- electionMsgs, _netman <- recorder, _netcmd <- netcmd

\* Set used for mapping Server to Integers, to compare ids from different servers.
\* VARIABLE idTable

serverVarsL == <<state, currentEpoch, lastProcessed, history>>

electionVarsL == <<currentVote, logicalClock, receiveVotes, outOfElection, recvQueue, waitNotmsg>>

leaderVarsL == <<leadingVoteSet>>

netVars == <<netcmd, recorder>>

electionNetVars == <<electionMsgs>>

varsLNoNet == <<serverVarsL, electionVarsL, leaderVarsL, historyVotes>>

varsL == <<serverVarsL, electionVarsL, leaderVarsL, electionNetVars, historyVotes>>

varsLL == <<varsL, netVars>>

----
\* update hist vote for inv check
UpdateHistVote ==
    IF currentVote = currentVote' THEN historyVotes ELSE 
    LET a == CHOOSE i \in Server: currentVote[i] /= currentVote'[i]
        isself == currentVote'[a].proposedLeader = a
        change == IF isself THEN historyVotes[a] ELSE Append(historyVotes[a], <<currentVote'[a], logicalClock'[a]>>)
        length ==  Len(historyVotes[a])
        ok ==    IF length <= 1 \/ isself  THEN TRUE
                 ELSE historyVotes[a][length][1] /= currentVote'[a] /\ currentVote'[a].proposedLeader /= a
                        => <<currentVote'[a], logicalClock'[a]>> \notin ToSet(SubSeq(historyVotes[a], 2, length))
    IN IF ok THEN [historyVotes EXCEPT ![a] = change] ELSE [historyVotes EXCEPT ![a] = <<FALSE>> \o change]

----
CheckLock(i) ==
    IF recorder.lock = INITING /\ Cardinality(recorder.init) > 1 THEN INITING ELSE
    IF Len(recvQueue'[i]) /= 0 THEN i ELSE NONE

CheckInit(i) ==
    IF recorder.lock = INITING THEN recorder.init \ {i} ELSE recorder.init

\* net args for every step
Net1Args(i) == [lock |-> CheckLock(i), init |-> CheckInit(i)]

Net1NoAction(pc) == net1!NetNoActionArgCmd(Net1Args(pc[2]), pc)
Net1NoActionArg(pc, arg) == net1!NetNoActionArgCmd(arg @@ Net1Args(pc[2]), pc)

FConnArg(i, j) == [ zabLock |-> "fconn", zabLockArgs |-> <<i, j>>]
-----------------------------------------------------------------------------
\* Processing of electionMsgs
\* BroadcastNotmsg(i, m) == electionMsgs' = [electionMsgs EXCEPT ![i] = [v \in Server |-> IF v /= i
\*                                                                                        THEN Append(electionMsgs[i][v], m)
\*                                                                                        ELSE electionMsgs[i][v]]]
RecorderIncTimeout == net1!_NetIncHelper("nTimeout")
BroadcastNotmsg(i, m) == net1!NetArg(Net1Args(i), net1!NetBatchAddMsgDsts(i, Server \ {i}, m))
TimeoutBroadcastNotmsg(i, m) == net1!NetArg(RecorderIncTimeout @@ Net1Args(i), net1!NetBatchAddMsgDsts(i, Server \ {i}, m))

\* DiscardNotmsg(i, j) == electionMsgs' = [electionMsgs EXCEPT ![i][j] = IF electionMsgs[i][j] /= << >>
\*                                                                       THEN Tail(electionMsgs[i][j])
\*                                                                       ELSE << >>]
DiscardNotmsg(i, j) == net1!NetArg(Net1Args(j), net1!NetDelSrcDstMsg(i, j))

\* ReplyNotmsg(i, j, m) == electionMsgs' = [electionMsgs EXCEPT ![i][j] = Append(electionMsgs[i][j], m),
\*                                                              ![j][i] = Tail(electionMsgs[j][i])]
ReplyNotmsg(i, j, m) == net1!NetArg(Net1Args(i), net1!NetReplySrcDstMsg(i, j, m))

-----------------------------------------------------------------------------
\* Processing of recvQueue
RECURSIVE RemoveNone(_)
RemoveNone(seq) == CASE seq =  << >> -> << >>
                   []   seq /= << >> -> IF Head(seq).mtype = NONE THEN RemoveNone(Tail(seq))
                                                                  ELSE <<Head(seq)>> \o RemoveNone(Tail(seq))

IdCompare(id1, id2) == ServerOrd[id1] > ServerOrd[id2]

\* FALSE: zxid1 <= zxid2; TRUE: zxid1 > zxid2
ZxidCompare(zxid1, zxid2) == \/ zxid1[1] > zxid2[1]
                             \/ /\ zxid1[1] = zxid2[1]
                                /\ zxid1[2] > zxid2[2]

ZxidEqual(zxid1, zxid2) == zxid1[1] = zxid2[1] /\ zxid1[2] = zxid2[2]

\* FALSE: vote1 <= vote2; TRUE: vote1 > vote2
TotalOrderPredicateCorrect(vote1, vote2) == \/ vote1.proposedEpoch > vote2.proposedEpoch
                                            \/ /\ vote1.proposedEpoch = vote2.proposedEpoch
                                               /\ \/ ZxidCompare(vote1.proposedZxid, vote2.proposedZxid)
                                                  \/ /\ ZxidEqual(vote1.proposedZxid, vote2.proposedZxid)
                                                     /\ IdCompare(vote1.proposedLeader, vote2.proposedLeader)

\* \* Bug: ZOOKEEPER-1419
TotalOrderPredicateBug(vote1, vote2) == \/ vote1.proposedEpoch > vote2.proposedEpoch
                                        \/ /\ vote1.proposedEpoch = vote2.proposedEpoch
                                           /\ ZxidCompare(vote1.proposedZxid, vote2.proposedZxid)
                                        \/ /\ ZxidEqual(vote1.proposedZxid, vote2.proposedZxid)
                                           /\ IdCompare(vote1.proposedLeader, vote2.proposedLeader)
TotalOrderPredicate(vote1, vote2) ==
    IF CheckParameterTrue("DisableBug1419")
    THEN TotalOrderPredicateCorrect(vote1, vote2)
    ELSE TotalOrderPredicateBug(vote1, vote2)

VoteEqual(vote1, round1, vote2, round2) == /\ vote1.proposedLeader = vote2.proposedLeader
                                           /\ ZxidEqual(vote1.proposedZxid, vote2.proposedZxid)
                                           /\ vote1.proposedEpoch  = vote2.proposedEpoch
                                           /\ round1 = round2

InitLastProcessed(i) == IF Len(history[i]) = 0 THEN [ index |-> 0, 
                                                 zxid |-> <<0, 0>> ]
                        ELSE
                        LET lastIndex == Len(history[i])
                            entry     == history[i][lastIndex]
                        IN [ index |-> lastIndex,
                             zxid  |-> entry.zxid ]

RECURSIVE InitAcksidInTxns(_,_)
InitAcksidInTxns(txns, src) == IF Len(txns) = 0 THEN << >>
                               ELSE LET newTxn == [ zxid   |-> txns[1].zxid,
                                                    value  |-> txns[1].value,
                                                    ackSid |-> {src},
                                                    epoch  |-> txns[1].epoch ]
                                    IN <<newTxn>> \o InitAcksidInTxns( Tail(txns), src)

InitHistory(i) == LET newState == state'[i] IN 
                    IF newState = LEADING THEN InitAcksidInTxns(history[i], i)
                    ELSE history[i]
-----------------------------------------------------------------------------
\* Processing of currentVote
InitialVote == [proposedLeader |-> NullPoint,
                proposedZxid   |-> <<0, 0>>,
                proposedEpoch  |-> 0]

SelfVote(i) == [proposedLeader |-> i,
                proposedZxid   |-> lastProcessed[i].zxid,
                proposedEpoch  |-> currentEpoch[i]]

UpdateProposal(i, nid, nzxid, nepoch) == currentVote' = [currentVote EXCEPT ![i].proposedLeader = nid, \* no need to record state in LOOKING
                                                                            ![i].proposedZxid   = nzxid,
                                                                            ![i].proposedEpoch  = nepoch]

-----------------------------------------------------------------------------
\* Processing of receiveVotes and outOfElection
RvClear(i) == receiveVotes'  = [receiveVotes  EXCEPT ![i] = [v \in Server |-> [vote    |-> InitialVote,
                                                                               round   |-> 0,
                                                                               state   |-> LOOKING,
                                                                               version |-> 0]]]

RvPut(i, id, mvote, mround, mstate) == receiveVotes' = CASE receiveVotes[i][id].round < mround -> [receiveVotes EXCEPT ![i][id].vote    = mvote,
                                                                                                                       ![i][id].round   = mround,
                                                                                                                       ![i][id].state   = mstate,
                                                                                                                       ![i][id].version = 1]
                                                       []   receiveVotes[i][id].round = mround -> [receiveVotes EXCEPT ![i][id].vote    = mvote,
                                                                                                                       ![i][id].state   = mstate,
                                                                                                                       ![i][id].version = @ + 1]
                                                       []   receiveVotes[i][id].round > mround -> receiveVotes

Put(i, id, rcvset, mvote, mround, mstate) == CASE rcvset[id].round < mround -> [rcvset EXCEPT ![id].vote    = mvote,
                                                                                              ![id].round   = mround,
                                                                                              ![id].state   = mstate,
                                                                                              ![id].version = 1]
                                             []   rcvset[id].round = mround -> [rcvset EXCEPT ![id].vote    = mvote,
                                                                                              ![id].state   = mstate,
                                                                                              ![id].version = @ + 1]
                                             []   rcvset[id].round > mround -> rcvset

RvClearAndPut(i, id, vote, round) == receiveVotes' = LET oneVote == [vote    |-> vote, 
                                                                     round   |-> round, 
                                                                     state   |-> LOOKING,
                                                                     version |-> 1]
                                                     IN [receiveVotes EXCEPT ![i] = [v \in Server |-> IF v = id THEN oneVote
                                                                                                                ELSE [vote    |-> InitialVote,
                                                                                                                      round   |-> 0,
                                                                                                                      state   |-> LOOKING,
                                                                                                                      version |-> 0]]]                     

VoteSet(i, msource, rcvset, thisvote, thisround) == {msource} \union {s \in (Server \ {msource}): VoteEqual(rcvset[s].vote, 
                                                                                                            rcvset[s].round,
                                                                                                            thisvote,
                                                                                                            thisround)}

HasQuorums(i, msource, rcvset, thisvote, thisround) == LET Q == VoteSet(i, msource, rcvset, thisvote, thisround)
                                                       IN IF Q \in Quorums THEN TRUE ELSE FALSE

\* v3.7.0
CheckLeader(i, votes, thisleader, thisround) == IF thisleader = i THEN (IF thisround = logicalClock[i] THEN TRUE ELSE FALSE)
                                                ELSE (IF votes[thisleader].vote.proposedLeader = NullPoint THEN FALSE
                                                      ELSE (IF votes[thisleader].state = LEADING THEN TRUE 
                                                                                                 ELSE FALSE))

\* v3.4.3
\* CheckLeader(i, votes, thisleader, thisround) == IF thisleader = i THEN TRUE
\*                                                 ELSE (IF votes[thisleader].vote.proposedLeader = NullPoint THEN FALSE
\*                                                       ELSE (IF votes[thisleader].state = LEADING THEN TRUE 
\*                                                                                                  ELSE FALSE))

OoeClear(i) == outOfElection' = [outOfElection EXCEPT ![i] = [v \in Server |-> [vote    |-> InitialVote,
                                                                                round   |-> 0,
                                                                                state   |-> LOOKING,
                                                                                version |-> 0]]]  

OoePut(i, id, mvote, mround, mstate) == outOfElection' = CASE outOfElection[i][id].round < mround -> [outOfElection EXCEPT ![i][id].vote    = mvote,
                                                                                                                           ![i][id].round   = mround,
                                                                                                                           ![i][id].state   = mstate,
                                                                                                                           ![i][id].version = 1]
                                                         []   outOfElection[i][id].round = mround -> [outOfElection EXCEPT ![i][id].vote    = mvote,
                                                                                                                           ![i][id].state   = mstate,
                                                                                                                           ![i][id].version = @ + 1]
                                                         []   outOfElection[i][id].round > mround -> outOfElection

-----------------------------------------------------------------------------    
InitServerVarsL ==
                \* /\ state         = [s \in Server |-> INITING]
                   /\ state         = [s \in Server |-> LOOKING]
                   /\ currentEpoch  = IF CheckParameterTrue("DisableInitBug1419")
                                      THEN [s \in Server |-> 0]
                                      ELSE LET s == CHOOSE s \in Server: TRUE
                                           IN ( s :> 1) @@ [x \in Server \ {s} |-> 0]  \* Set a bug init state
                \* /\ currentEpoch = LET s == CHOOSE s \in Server: TRUE
                \*                   IN ( s :> 1) @@ [x \in Server \ {s} |-> 0]  \* Set a init state
                \* /\ currentEpoch = LET s == CHOOSE s \in Server: (\E i,j \in Server: ServerOrd[i] < ServerOrd[s] /\ ServerOrd[s] < ServerOrd[j])
                \*                   IN ( s :> 1) @@ [x \in Server \ {s} |-> 0]  \* Set a init state 
                   /\ lastProcessed = [s \in Server |-> [index |-> 0,
                                                         zxid  |-> <<0, 0>>] ]
                   /\ history       = [s \in Server |-> << >>]

InitElectionVarsL == /\ currentVote   = [s \in Server |-> SelfVote(s)]
                     /\ logicalClock  = [s \in Server |-> 0]
                     /\ receiveVotes  = [s \in Server |-> [v \in Server |-> [vote    |-> InitialVote,
                                                                             round   |-> 0,
                                                                             state   |-> LOOKING,
                                                                             version |-> 0]]]
                     /\ outOfElection = [s \in Server |-> [v \in Server |-> [vote    |-> InitialVote,
                                                                             round   |-> 0,
                                                                             state   |-> LOOKING,
                                                                             version |-> 0]]]
                     /\ recvQueue     = [s \in Server |-> << >>]
                     /\ waitNotmsg    = [s \in Server |-> FALSE]
                     /\ historyVotes = [ i \in Server |-> <<TRUE>> ]


InitLeaderVarsL == leadingVoteSet = [s \in Server |-> {}]

InitL ==/\ InitServerVarsL
        /\ InitElectionVarsL
        /\ InitLeaderVarsL
        /\ net1!InitFifoNetworkAddNetman(Server, <<"Init">>, [lock |-> INITING, init |-> Server, nTimeout  |-> 0])

-----------------------------------------------------------------------------
(* The beginning part of FLE's main function lookForLeader() *)
ZabFLEResetInit(i, reset) ==
        /\ state'          = [state          EXCEPT ![i] = LOOKING]
        /\ lastProcessed'  = [lastProcessed  EXCEPT ![i] = InitLastProcessed(i)]
        /\ logicalClock'   = [logicalClock   EXCEPT ![i] = IF reset THEN 0 ELSE logicalClock[i] + 1]
        /\ currentVote'    = [currentVote    EXCEPT ![i] = [proposedLeader |-> i,
                                                            proposedZxid   |-> lastProcessed'[i].zxid,
                                                            proposedEpoch  |-> currentEpoch[i]]]
        /\ receiveVotes'   = [receiveVotes   EXCEPT ![i] = [v \in Server |-> [vote    |-> InitialVote,
                                                                              round   |-> 0,
                                                                              state   |-> LOOKING,
                                                                              version |-> 0]]]
        /\ outOfElection'  = [outOfElection  EXCEPT ![i] = [v \in Server |-> [vote    |-> InitialVote,
                                                                              round   |-> 0,
                                                                              state   |-> LOOKING,
                                                                              version |-> 0]]]
        /\ recvQueue'      = [recvQueue      EXCEPT ![i] = << >>]  
        /\ waitNotmsg'     = [waitNotmsg     EXCEPT ![i] = FALSE]
        /\ leadingVoteSet' = [leadingVoteSet EXCEPT ![i] = {}]
        /\ UNCHANGED <<currentEpoch, history>>

ZabFLEBroadcast(i) ==
    /\ net1!NetUpdate2(BroadcastNotmsg(i, [mtype |-> NOTIFICATION,
                                                msource |-> i,
                                                mstate  |-> LOOKING,
                                                mround  |-> logicalClock'[i],
                                                mvote   |-> currentVote'[i]]),
                       <<"ZabTimeout", i>>)

ZabFLEBroadcastNoUpdate(i) ==
    BroadcastNotmsg(i, [mtype |-> NOTIFICATION, msource |-> i,
                                                mstate  |-> LOOKING,
                                                mround  |-> logicalClock'[i],
                                                mvote   |-> currentVote'[i]])

ZabTimeout(i) ==
        \* /\ state[i] \in {LEADING, FOLLOWING}
        \* /\ state[i] = INITING
        /\ ZabFLEResetInit(i, FALSE)
        /\ ZabFLEBroadcast(i)

(* Abstraction of WorkerReceiver.run() *)
ReceiveNotmsg(i, j) ==
        /\ electionMsgs[j][i] /= << >>
        /\ UNCHANGED <<serverVarsL, currentVote, logicalClock, receiveVotes, outOfElection, waitNotmsg, leaderVarsL>>
        /\ LET notmsg == electionMsgs[j][i][1]
               toSend == [mtype   |-> NOTIFICATION,
                          msource |-> i,
                          mstate  |-> state[i],
                          mround  |-> logicalClock[i],
                          mvote   |-> currentVote[i]]
           IN \/ /\ state[i] = LOOKING
                 /\ recvQueue' = [recvQueue EXCEPT ![i] = Append(RemoveNone(recvQueue[i]), notmsg)]
                 /\ LET replyOk == /\ notmsg.mstate = LOOKING
                                   /\ notmsg.mround < logicalClock[i]
                    IN 
                    \/ /\ replyOk
                       /\ net1!NetUpdate2(ReplyNotmsg(i, j, toSend), <<"ReceiveNotmsg", i, j, "LOOKING reply">>)
                    \/ /\ ~replyOk
                       /\ net1!NetUpdate2(DiscardNotmsg(j, i), <<"ReceiveNotmsg", i, j, "LOOKING not reply">>)
              \/ /\ state[i] \in {LEADING, FOLLOWING}
                 /\ UNCHANGED recvQueue
                 /\ \/ \* Only reply when sender's state is LOOKING
                       /\ notmsg.mstate = LOOKING
                       /\ net1!NetUpdate2(ReplyNotmsg(i, j, toSend), <<"ReceiveNotmsg", i, j, "not LOOKING and reply">>)
                    \/ \* sender's state and mine are both not LOOKING, just discard
                       /\ notmsg.mstate /= LOOKING
                       /\ net1!NetUpdate2(DiscardNotmsg(j, i), <<"ReceiveNotmsg", i, j, "not LOOKING">>)

NotmsgTimeout(i) == 
        /\ state[i] = LOOKING
        /\ \A j \in Server \ {i}: electionMsgs[j][i] = << >>
        /\ recvQueue[i] = << >>
        \* /\ recvQueue' = [recvQueue EXCEPT ![i] = Append(recvQueue[i], [mtype |-> NONE])]
        \* /\ net1!NetUpdate(Net1NoAction(i, <<"NotmsgTimeout", i>>))
        \* /\ UNCHANGED <<serverVarsL, currentVote, logicalClock, receiveVotes, outOfElection, waitNotmsg, leaderVarsL>>

        /\    /\ \lnot waitNotmsg[i]
              /\ LET rawToSend == [ mtype   |-> NOTIFICATION,
                                    msource |-> i,
                                    mstate  |-> LOOKING,
                                    mround  |-> logicalClock[i],
                                    mvote   |-> currentVote[i]]
                 IN /\ UNCHANGED <<serverVarsL, currentVote, logicalClock, receiveVotes, outOfElection, waitNotmsg, leaderVarsL, recvQueue>>
                    /\ net1!NetUpdate2(TimeoutBroadcastNotmsg(i, rawToSend), <<"NotmsgTimeout", i>>)

-----------------------------------------------------------------------------
\* Sub-action in HandleNotmsg
\* v3.7.0
\* ReceivedFollowingAndLeadingNotification(i, n) ==
\*         LET newVotes    == Put(i, n.msource, receiveVotes[i], n.mvote, n.mround, n.mstate)
\*             voteSet1    == VoteSet(i, n.msource, newVotes, n.mvote, n.mround)
\*             hasQuorums1 == voteSet1 \in Quorums
\*             check1      == CheckLeader(i, newVotes, n.mvote.proposedLeader, n.mround)
\*             leaveOk1    == /\ n.mround = logicalClock[i]
\*                            /\ hasQuorums1
\*                            /\ check1    \* state and leadingVoteSet cannot be changed twice in the first '/\' and second '/\'.
\*         IN
\*         /\ \/ /\ n.mround = logicalClock[i]
\*               /\ receiveVotes' = [receiveVotes EXCEPT ![i] = newVotes]
\*            \/ /\ n.mround /= logicalClock[i]
\*               /\ UNCHANGED receiveVotes
\*         /\ \/ /\ leaveOk1
\*               \* /\ PrintT("leave with condition 1")
\*               /\ state' = [state EXCEPT ![i] = IF n.mvote.proposedLeader = i THEN LEADING ELSE FOLLOWING]
\*               /\ leadingVoteSet' = [leadingVoteSet EXCEPT ![i] = IF n.mvote.proposedLeader = i THEN voteSet1 ELSE @]
\*               /\ UpdateProposal(i, n.mvote.proposedLeader, n.mvote.proposedZxid, n.mvote.proposedEpoch)
\*               /\ UNCHANGED <<logicalClock, outOfElection>>
\*            \/ /\ ~leaveOk1
\*               /\ outOfElection' = [outOfElection EXCEPT ![i] = Put(i, n.msource, outOfElection[i], n.mvote,n.mround, n.mstate)]
\*               /\ LET voteSet2    == VoteSet(i, n.msource, outOfElection'[i], n.mvote, n.mround)
\*                      hasQuorums2 == voteSet2 \in Quorums
\*                      check2      == CheckLeader(i, outOfElection'[i], n.mvote.proposedLeader, n.mround)
\*                      leaveOk2    == /\ hasQuorums2
\*                                     /\ check2
\*                  IN
\*                  \/ /\ leaveOk2
\*                     \* /\ PrintT("leave with condition 2")
\*                     /\ logicalClock' = [logicalClock EXCEPT ![i] = n.mround]
\*                     /\ state' = [state EXCEPT ![i] = IF n.mvote.proposedLeader = i THEN LEADING ELSE FOLLOWING]
\*                     /\ leadingVoteSet' = [leadingVoteSet EXCEPT ![i] = IF n.mvote.proposedLeader = i THEN voteSet2 ELSE @]
\*                     /\ UpdateProposal(i, n.mvote.proposedLeader, n.mvote.proposedZxid, n.mvote.proposedEpoch)
\*                  \/ /\ ~leaveOk2
\*                     /\ LET leaveOk3 == /\ n.mstate = LEADING
\*                                        /\ n.mround = logicalClock[i]
\*                        IN
\*                        \/ /\ leaveOk3
\*                           \* /\ PrintT("leave with condition 3")
\*                           /\ state' = [state EXCEPT ![i] = IF n.mvote.proposedLeader = i THEN LEADING ELSE FOLLOWING]
\*                           /\ UpdateProposal(i, n.mvote.proposedLeader, n.mvote.proposedZxid, n.mvote.proposedEpoch)
\*                        \/ /\ ~leaveOk3
\*                           /\ UNCHANGED <<state, currentVote>>
\*                     /\ UNCHANGED <<logicalClock, leadingVoteSet>>

\* v3.4.3
ReceivedFollowingAndLeadingNotification(i, n) ==
        LET newVotes    == Put(i, n.msource, receiveVotes[i], n.mvote, n.mround, n.mstate)
            voteSet1    == VoteSet(i, n.msource, newVotes, n.mvote, n.mround)
            hasQuorums1 == voteSet1 \in Quorums
            \* v3.7.0
            check1      == CheckLeader(i, newVotes, n.mvote.proposedLeader, n.mround)
            \* v3.4.3
            \* check1      == CheckLeader(i, outOfElection[i], n.mvote.proposedLeader, n.mround)
            leaveOk1    == /\ n.mround = logicalClock[i]
                           /\ hasQuorums1
                           /\ check1    \* state and leadingVoteSet cannot be changed twice in the first '/\' and second '/\'.
        IN
        /\ \/ /\ n.mround = logicalClock[i]
              /\ receiveVotes' = [receiveVotes EXCEPT ![i] = newVotes]
           \/ /\ n.mround /= logicalClock[i]
              /\ UNCHANGED receiveVotes
        /\ \/ /\ leaveOk1
              \* /\ PrintT("leave with condition 1")
              /\ state' = [state EXCEPT ![i] = IF n.mvote.proposedLeader = i THEN LEADING ELSE FOLLOWING]
              /\ leadingVoteSet' = [leadingVoteSet EXCEPT ![i] = IF n.mvote.proposedLeader = i THEN voteSet1 ELSE @]
              /\ UpdateProposal(i, n.mvote.proposedLeader, n.mvote.proposedZxid, n.mvote.proposedEpoch)
              \* /\ UNCHANGED <<leadingVoteSet, currentVote>>
              /\ UNCHANGED <<logicalClock, outOfElection>>
              /\ IF state'[i] = FOLLOWING THEN net1!NetUpdate(Net1NoActionArg(<<"HandleNotmsg", i, "leaveOk1">>, FConnArg(n.mvote.proposedLeader, i)))
                 ELSE net1!NetUpdate(Net1NoAction(<<"HandleNotmsg", i, "leaveOk1">>))
           \/ /\ ~leaveOk1
              /\ outOfElection' = [outOfElection EXCEPT ![i] = Put(i, n.msource, outOfElection[i], n.mvote,n.mround, n.mstate)]
              /\ LET voteSet2    == VoteSet(i, n.msource, outOfElection'[i], n.mvote, n.mround)
                     hasQuorums2 == voteSet2 \in Quorums
                     check2      == CheckLeader(i, outOfElection'[i], n.mvote.proposedLeader, n.mround)
                     leaveOk2    == /\ hasQuorums2
                                    /\ check2
                 IN
                 \/ /\ leaveOk2
                    \* /\ PrintT("leave with condition 2")
                    /\ logicalClock' = [logicalClock EXCEPT ![i] = n.mround]
                    /\ state' = [state EXCEPT ![i] = IF n.mvote.proposedLeader = i THEN LEADING ELSE FOLLOWING]
                    /\ leadingVoteSet' = [leadingVoteSet EXCEPT ![i] = IF n.mvote.proposedLeader = i THEN voteSet2 ELSE @]
                    /\ UpdateProposal(i, n.mvote.proposedLeader, n.mvote.proposedZxid, n.mvote.proposedEpoch)
                    \* /\ UNCHANGED <<leadingVoteSet, currentVote>>
                    /\ IF state'[i] = FOLLOWING THEN net1!NetUpdate(Net1NoActionArg(<<"HandleNotmsg", i, "leaveOk2">>, FConnArg(n.mvote.proposedLeader, i)))
                       ELSE net1!NetUpdate(Net1NoAction(<<"HandleNotmsg", i, "leaveOk2">>))
                    \* /\ net1!NetUpdate(Net1NoAction(<<"HandleNotmsg", i, "leaveOk2">>))
                 \/ /\ ~leaveOk2
                    /\ UNCHANGED <<state, currentVote>>
                    \* v3.8.0  (two nodes config, using oracle)
                    \* /\ LET leaveOk3 == /\ n.mstate = LEADING
                    \*                    /\ n.mround = logicalClock[i]
                    \*    IN
                    \*    \/ /\ leaveOk3
                    \*       \* /\ PrintT("leave with condition 3")
                    \*       /\ state' = [state EXCEPT ![i] = IF n.mvote.proposedLeader = i THEN LEADING ELSE FOLLOWING]
                    \*       /\ UpdateProposal(i, n.mvote.proposedLeader, n.mvote.proposedZxid, n.mvote.proposedEpoch)
                    \*    \/ /\ ~leaveOk3
                    \*       /\ UNCHANGED <<state, currentVote>>
                    /\ UNCHANGED <<logicalClock, leadingVoteSet>>
                    /\ net1!NetUpdate(Net1NoAction(<<"HandleNotmsg", i, "not leaveOk">>))

(* Main part of lookForLeader() *)
HandleNotmsg(i) ==
        /\ state[i] = LOOKING
        /\ \lnot waitNotmsg[i]
        /\ recvQueue[i] /= << >>
        /\ UNCHANGED <<currentEpoch, lastProcessed>>
        /\ recvQueue' = [recvQueue EXCEPT ![i] = Tail(recvQueue[i])]
        /\ LET n         == recvQueue[i][1]
               rawToSend == [mtype   |-> NOTIFICATION,
                             msource |-> i,
                             mstate  |-> LOOKING,
                             mround  |-> logicalClock[i],
                             mvote   |-> currentVote[i]]
           IN \/ /\ n.mtype = NONE
                 /\ UNCHANGED <<history, logicalClock, currentVote, receiveVotes, waitNotmsg, outOfElection, state, leadingVoteSet>>
                 /\ net1!NetUpdate2(BroadcastNotmsg(i, rawToSend), <<"HandleNotmsg", i, "process NONE">>)
              \/ /\ n.mtype = NOTIFICATION
                 /\ \/ /\ n.mstate = LOOKING
                       /\ UNCHANGED <<state, history, outOfElection, leadingVoteSet>>
                       /\ \/ \* n.round >= my round, then update data and receiveVotes.
                             /\ n.mround >= logicalClock[i]
                             /\ \/ \* n.round > my round, update round and decide new proposed leader.
                                   /\ n.mround > logicalClock[i]
                                   /\ logicalClock' = [logicalClock EXCEPT ![i] = n.mround] \* There should be RvClear, we will handle it in the following.
                                   /\ LET selfinfo == [proposedLeader |-> i,
                                                       proposedZxid   |-> lastProcessed[i].zxid,
                                                       proposedEpoch  |-> currentEpoch[i]]
                                          peerOk   == TotalOrderPredicate(n.mvote, selfinfo)
                                      IN /\ \/ /\ peerOk
                                               /\ UpdateProposal(i, n.mvote.proposedLeader, n.mvote.proposedZxid, n.mvote.proposedEpoch)
                                            \/ /\ ~peerOk
                                               /\ UpdateProposal(i, i, lastProcessed[i].zxid, currentEpoch[i])
                                         /\ net1!NetUpdate2(BroadcastNotmsg(i, [mtype   |-> NOTIFICATION,
                                                                msource |-> i,
                                                                mstate  |-> LOOKING,
                                                                mround  |-> n.mround,
                                                                mvote   |-> currentVote'[i]]),
                                                            <<"HandleNotmsg", i, peerOk, "n.round bigger">>)
                                \/ \* n.round = my round & n.vote > my vote
                                   /\ n.mround = logicalClock[i]
                                   /\ UNCHANGED logicalClock
                                   /\ LET peerOk == TotalOrderPredicate(n.mvote, currentVote[i])
                                      IN \/ /\ peerOk
                                            /\ UpdateProposal(i, n.mvote.proposedLeader, n.mvote.proposedZxid, n.mvote.proposedEpoch)
                                            /\ net1!NetUpdate2(BroadcastNotmsg(i, [mtype   |-> NOTIFICATION,
                                                                   msource |-> i,
                                                                   mstate  |-> LOOKING,
                                                                   mround  |-> logicalClock[i],
                                                                   mvote   |-> n.mvote]),
                                                                <<"HandleNotmsg", i, "n.vote bigger">>)
                                         \/ /\ ~peerOk
                                            /\ UNCHANGED <<currentVote>>
                                            /\ net1!NetUpdate(Net1NoAction(<<"HandleNotmsg", i, "n.vote smaller">>))
                             /\ LET rcvsetModifiedTwice == n.mround > logicalClock[i]
                                IN \/ /\ rcvsetModifiedTwice   \* Since a variable cannot be changed more than once in one action, we handle receiveVotes here.
                                      /\ RvClearAndPut(i, n.msource, n.mvote, n.mround)  \* clear + put
                                   \/ /\ ~rcvsetModifiedTwice
                                      /\ RvPut(i, n.msource, n.mvote, n.mround, n.mstate)          \* put
                             /\ LET hasQuorums == HasQuorums(i, i, receiveVotes'[i], currentVote'[i], n.mround)
                                IN \/ /\ hasQuorums \* If hasQuorums, see action WaitNewNotmsg and WaitNewNotmsgEnd.
                                      /\ waitNotmsg' = [waitNotmsg EXCEPT ![i] = TRUE] 
                                   \/ /\ ~hasQuorums                            
                                      /\ UNCHANGED waitNotmsg
                          \/ \* n.round < my round, just discard it.
                             /\ n.mround < logicalClock[i]
                             /\ UNCHANGED <<logicalClock, currentVote, receiveVotes, waitNotmsg>>
                             /\ net1!NetUpdate(Net1NoAction(<<"HandleNotmsg", i, "n.round smaller">>))
                    \/ \* mainly contains receivedFollowingNotification(line 1146), receivedLeadingNotification(line 1185).
                       /\ n.mstate \in {LEADING, FOLLOWING}
                       /\ UNCHANGED <<waitNotmsg>>
                       /\ ReceivedFollowingAndLeadingNotification(i, n)
                       /\ history' = [history EXCEPT ![i] = InitHistory(i) ]
        /\ IF recvQueue[i][1].mtype /= NONE /\ recvQueue[i][1].mstate \in {LEADING, FOLLOWING}
           THEN historyVotes' = [historyVotes EXCEPT ![i] = <<TRUE>>]
           ELSE historyVotes' = UpdateHistVote

\* On the premise that ReceiveVotes.HasQuorums = TRUE, corresponding to logic in FLE.java.
\* Line 813
WaitNewNotmsg(i) ==
        /\ state[i] = LOOKING
        /\ waitNotmsg[i] = TRUE
        /\ \/ /\ recvQueue[i] /= << >>
              /\ recvQueue[i][1].mtype = NOTIFICATION
              /\ UNCHANGED <<serverVarsL, currentVote, logicalClock, receiveVotes, outOfElection, leaderVarsL>>
              /\ LET n == recvQueue[i][1]
                     peerOk == TotalOrderPredicate(n.mvote, currentVote[i])
                 IN /\ \/ /\ peerOk
                          /\ waitNotmsg' = [waitNotmsg EXCEPT ![i] = FALSE]
                          /\ recvQueue'  = [recvQueue  EXCEPT ![i] = Append(Tail(@), n)]
                       \/ /\ ~peerOk
                          /\ recvQueue' = [recvQueue EXCEPT ![i] = Tail(@)]
                          /\ UNCHANGED waitNotmsg
                    /\ net1!NetUpdate(Net1NoAction(<<"WaitNewNotmsg", i, peerOk, "NOTIFICATION">>))
           \/ /\ \/ recvQueue[i] = << >>
                 \/ /\ recvQueue[i] /= << >>
                    /\ recvQueue[i][1].mtype = NONE
              /\ currentVote[i].proposedLeader /= i => state[currentVote[i].proposedLeader] = LEADING  \* let leader timeout first
                                                        \* \/ ~\E j \in Server \ {i}: waitNotmsg[j] = TRUE  \* no possible leader to timeout, i timeout
              /\ state' = [state EXCEPT ![i] = IF currentVote[i].proposedLeader = i THEN LEADING
                                               ELSE FOLLOWING ]
              /\ leadingVoteSet' = [leadingVoteSet EXCEPT ![i] = 
                                                           IF currentVote[i].proposedLeader = i 
                                                           THEN VoteSet(i, i, receiveVotes[i], currentVote[i],
                                                                        logicalClock[i])
                                                           ELSE @]
              /\ history' = [history EXCEPT ![i] = InitHistory(i)]
              /\ UNCHANGED <<currentEpoch, lastProcessed, electionVarsL>>
              /\ LET lockArg == IF state'[i] = FOLLOWING THEN FConnArg(currentVote[i].proposedLeader, i) ELSE <<>>
                     args == RecorderIncTimeout @@ lockArg
                 IN net1!NetUpdate(Net1NoActionArg(<<"WaitNewNotmsg", i, state'[i], "timeout">>, args))
-----------------------------------------------------------------------------

FleIsOn(i) == TRUE

FlePostCond(i) == TRUE

IsFleLocked == recorder.lock \notin {NONE, INITING}
IsNotFLE == recorder.lock = NONE

FleZabTimeout(precond(_), postcond(_)) ==
           /\ recorder.lock = INITING
           /\ LET i == CHOOSE i \in recorder.init: TRUE
              IN /\ precond(i)
                 /\ ZabTimeout(i)
                 /\ postcond(i)
           /\ historyVotes' = UpdateHistVote

FleReceiveNotmsg(precond(_), postcond(_)) ==
           /\ recorder.lock = NONE
           /\ \E i, j \in Server:
                /\ i /= j
                /\ precond(i)
                /\ ReceiveNotmsg(i, j)
                /\ postcond(i)
           /\ historyVotes' = UpdateHistVote

FleNotmsgTimeout(precond(_), postcond(_)) ==
           /\ recorder.lock = NONE
           /\ \E i \in Server:
                /\ precond(i)
                /\ NotmsgTimeout(i)
                /\ postcond(i)
           /\ historyVotes' = UpdateHistVote

FleHandleNotmsgOrWaitNewNotmsg(precond(_), postcond(_)) ==
    /\ recorder.lock /= INITING
    /\     LET s == IF IsFleLocked THEN {recorder.lock} ELSE Server
           IN \E i \in s:
               /\ precond(i)
               /\
                  \/ /\ HandleNotmsg(i)
                     /\ postcond(i)
                  \/ /\ WaitNewNotmsg(i)
                     /\ historyVotes' = UpdateHistVote
                     /\ postcond(i)

NextL == 
        \/ FleZabTimeout(FleIsOn, FlePostCond)
        \/ FleReceiveNotmsg(FleIsOn, FlePostCond)
        \/ FleNotmsgTimeout(FleIsOn, FlePostCond)
        \/ FleHandleNotmsgOrWaitNewNotmsg(FleIsOn, FlePostCond)

SpecL == InitL /\ [][NextL]_varsLL

----
\* inv

NoVoteCircle ==
    \A i \in Server: historyVotes[i][1] = TRUE

=============================================================================
\* Modification History
\* Last modified Sat Jan 14 15:19:45 CST 2023 by huangbinyu
\* Last modified Sun Nov 14 15:18:32 CST 2021 by Dell
\* Created Fri Jun 18 20:23:47 CST 2021 by Dell

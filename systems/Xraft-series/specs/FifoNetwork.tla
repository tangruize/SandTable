---------------------------- MODULE FifoNetwork ----------------------------

EXTENDS Sequences, SequencesExt, Naturals, FiniteSets, TLC

(***************************************************************************
  VARIABLES definitions: see InitFifoNetwork
 ***************************************************************************)
VARIABLES _msgs,    \* Messages in the network
          _netman,  \* Network manager
          _netcmd   \* Current network cmd

(***************************************************************************
  FLUSH_DISCONN:
    * If true, drop all the network wired msgs that are not accessible
    * If false, do not drop, and msgs can still be delivered
 ***************************************************************************)
CONSTANT FLUSH_DISCONN

(***************************************************************************
  NULL_MSG: represent a null msg in some condition checkings
    * Should be a model value if its type is CONSTANT
 ***************************************************************************)
CONSTANT NULL_MSG
\*NULL_MSG == [ NULL_MSG |-> "" ]

---- \* Common functions

(***************************************************************************
  API InitFifoNetwork(nodes):
    - _msgs: init to emtpy sequences of [src][dst] records
      * format: [ src |-> s0, dst |-> s1, type |-> sth, data |-> sth]
      * src and dst will be dropped when storing in _msgs
      * type and data are user defined fields
    - _netman:
      - n_sent: number of msgs sent to network
      - n_recv: number of msgs delivered to server
      - n_wire: number of msgs in network but not delivered yet
      - conn: network connections
        * format: {n0, n1}, represents n0 is connected with n1
        * default all connnected
    - _netcmd: <<"init">>
 ***************************************************************************)
InitFifoNetworkAddNetmanNoMsgs(nodes, cmd, additionalNetman) ==
    /\ _netman = additionalNetman @@
                 [ n_sent |-> 0, n_recv |-> 0, n_wire |-> 0, conn |-> <<nodes>>,
                   n_part |-> 0, n_cure |-> 0]
    /\ _netcmd = <<cmd>>

InitFifoNetworkAddNetman(nodes, cmd, additionalNetman) ==
    /\ _msgs = [ sender \in nodes |-> [ recver \in nodes \ {sender} |-> <<>> ]]
    /\ _netman = additionalNetman @@
                 [ n_sent |-> 0, n_recv |-> 0, n_wire |-> 0, conn |-> <<nodes>>,
                   n_part |-> 0, n_cure |-> 0]
    /\ _netcmd = <<cmd>>

InitFifoNetwork(nodes) == InitFifoNetworkAddNetman(nodes, "init", <<>>)

(***************************************************************************
  _GetNodes: get all nodes in msg channels
 ***************************************************************************)
_GetNodes == DOMAIN _msgs

(***************************************************************************
  _Pick: choose any one
 ***************************************************************************)
_Pick(S) == CHOOSE s \in S : TRUE

(***************************************************************************
  API IsNullMsg: check if msg m is NULL 
 ***************************************************************************)
IsNullMsg(m) == m = NULL_MSG

---- \* Update _netman functions

(***************************************************************************
  _NetGetHelper and _NetIncHelper: get, inc and dec member of _netman records
 ***************************************************************************)
_NetGetHelper(member)    == _netman[member]
_NetIncHelper(member)    == (member :> _netman[member] + 1)
_NetDecHelper(member)    == (member :> _netman[member] - 1)
NetIncBy(member, number) == (member :> _netman[member] + number)
NetDecBy(member, number) == (member :> _netman[member] - number)

NetGetSent == _NetGetHelper("n_sent")
NetIncSent == _NetIncHelper("n_sent")
NetGetRecv == _NetGetHelper("n_recv")
NetIncRecv == _NetIncHelper("n_recv")
NetGetWire == _NetGetHelper("n_wire")
NetIncWire == _NetIncHelper("n_wire")
NetDecWire == _NetDecHelper("n_wire")
NetGetPart == _NetGetHelper("n_part")
NetIncPart == _NetIncHelper("n_part")
NetGetCure == _NetGetHelper("n_cure")
NetIncCure == _NetIncHelper("n_cure")

(***************************************************************************
  NetmanIncField: increase a field that is not a standard netman member
    * updater is the return value of NetDelMsg/NetAddMsg ..
 ***************************************************************************)
NetmanIncField(field, updater) ==
    <<_NetIncHelper(field) @@ updater[1]>> @@ updater 

(***************************************************************************
  _WireReduce, _WireNodeSumHelper, _WireSumHelper, NetSumWire:
    * Sum up wired msgs
 ***************************************************************************)
RECURSIVE _WireReduce(_, _, _, _)
_WireReduce(Helper(_, _, _), nodes, res, msgs) ==
    IF nodes = {} THEN res
    ELSE LET n == _Pick(nodes)
         IN _WireReduce(Helper, nodes \ {n}, Helper(n, res, msgs), msgs)

_WireNodeSumHelper(n, res, msgs) ==
    LET node_msgs_list == msgs[n]
    IN res + Len(node_msgs_list)

_WireSumHelper(n, res, msgs) ==
    LET node_msgs == msgs[n]
        to_nodes == DOMAIN node_msgs
    IN res + _WireReduce(_WireNodeSumHelper, to_nodes, 0, node_msgs)

_WireSum(msgs) ==
    [ n_wire |-> _WireReduce(_WireSumHelper, DOMAIN msgs, 0, msgs) ]

NetSumWire == _WireSum(_msgs)

(***************************************************************************
  API NetUpdate(args): update _netman with args[1], update _msgs with args[2]
    - e.g. NetUpdate(<<NetIncSent @@ NetIncWire, msgs, "send n1 n2">>)
 ***************************************************************************)
NetUpdate(args) ==
    /\ _netman' = args[1] @@ _netman
    /\ _msgs' = args[2]
    /\ IF Len(args) = 3
       THEN _netcmd' = args[3]
       ELSE _netcmd' = <<"noop">>

NetUpdate2(args, cmd) ==
    /\ _netman' = args[1] @@ _netman
    /\ _msgs' = args[2]
    /\ IF Len(args) = 3
       THEN _netcmd' = <<cmd, args[3]>>
       ELSE _netcmd' = <<cmd>>

---- \* Network partition functions

(***************************************************************************
  _AddConn: add nodes connections and return connected nodes
    * no change:
      * if nodes contain only one node, or
      * if nodes already connected
 ***************************************************************************)
_AddConn(nodes, conn) ==
    IF \/ Cardinality(nodes) <= 1
       \/ Len(SelectSeq(conn, LAMBDA p: nodes \subseteq p)) > 0
    THEN conn
    ELSE Append(SelectSeq(conn, LAMBDA p: \neg (p \subseteq nodes)), nodes)

_AddSingleNodeConn(node, conn) ==
    LET F[i \in 0..Len(conn)] ==
        IF i = 0 THEN <<>>
        ELSE LET already_all_connected == Len(F[i-1]) /= i-1
                 x == conn[i] \union {node}
                 all_connected == x = _GetNodes
             IN IF already_all_connected \/ all_connected THEN <<_GetNodes>>
                ELSE Append(F[i-1], x)
    IN F[Len(conn)]

(***************************************************************************
  _DelConn: isolate nodes from others and return connected nodes
    * delete node in nodes from all connections
    * if after deleting, the nodes set has no ndoe, delete the set
 ***************************************************************************)
_DelConn(nodes, conn) ==
    LET F[i \in 0..Len(conn)] == 
        IF i = 0 THEN <<>>
        ELSE IF Cardinality(conn[i] \ nodes) <= 0 THEN F[i-1]
             ELSE Append(F[i-1], conn[i] \ nodes)
        \* ELSE Append(F[i-1], conn[i] \ nodes)
        res == F[Len(conn)]
    IN IF Len(res) = 0 THEN <<{}>> ELSE res

(***************************************************************************
  _PartConn: delete nodes from other connections and then connect nodes
 ***************************************************************************)
_PartConn(nodes, conn) ==
    _AddConn(nodes, _DelConn(nodes, conn))

(***************************************************************************
  _FlushReduce, _FlushMsgsHelper, _FlushMsgs:
    * Flush disconnected msgs in wire
    * _FlushMsgs: Return flushed msgs
  _FlushMsgsDelHelper, _FlushMsgsDel:
    * All msgs are flushed in delete_nodes (not inner-connnected)
 ***************************************************************************)
RECURSIVE _FlushReduce(_, _, _, _, _)
_FlushReduce(Helper(_, _, _, _), nodes, res, part, msgs) ==
    IF nodes = {} THEN res
    ELSE LET n == _Pick(nodes)
         IN _FlushReduce(Helper, nodes \ {n}, Helper(n, res, part, msgs), part, msgs)

_FlushMsgsHelper(n, res, part, msgs) ==
    LET node_msgs == msgs[n]
        to_nodes == DOMAIN node_msgs
        flush_nodes == IF n \in part THEN to_nodes \ part ELSE part
    IN ( n :> ([ x \in flush_nodes |-> <<>> ] @@ node_msgs) ) @@ res

_FlushMsgsDelHelper(n, res, delete_nodes, msgs) ==
    LET node_msgs == msgs[n]
        to_nodes == DOMAIN node_msgs
        flush_nodes == IF n \in delete_nodes THEN to_nodes ELSE delete_nodes
    IN ( n :> ([ x \in flush_nodes |-> <<>> ] @@ node_msgs) ) @@ res

_FlushMsgs(part, msgs) ==
    _FlushReduce(_FlushMsgsHelper, DOMAIN msgs, msgs, part, msgs)

_FlushMsgsDel(delete_nodes, msgs) ==
    _FlushReduce(_FlushMsgsDelHelper, DOMAIN msgs, msgs, delete_nodes, msgs)

(***************************************************************************
  API NetAddConn: add a network connection
    * return <<netman, msgs, cmd>>
 ***************************************************************************)
NetAddConn(nodes) ==
    <<[ conn |-> _AddConn(nodes, _netman.conn) ], _msgs, <<"conn_add", nodes>>>>

NetAddSingleNodeConn(node) ==
    <<[ conn |-> _AddSingleNodeConn(node, _netman.conn) ], _msgs, <<"conn_add", node>>>> 

(***************************************************************************
  API NetDelConn: isolate nodes from all other nodes
    * unlike NetPartConn, nodes in the deletion set are not connected
 ***************************************************************************)
NetDelConn(nodes) ==
    LET conn == [ conn |-> _DelConn(nodes, _netman.conn) ]
    IN IF FLUSH_DISCONN
       THEN LET msgs == _FlushMsgsDel(nodes, _msgs)
                msgs_sum == _WireSum(msgs)
            IN <<conn @@ msgs_sum, msgs, <<"conn_del_flush", nodes>>>>
       ELSE <<conn, _msgs, <<"conn_del", nodes>>>>

(***************************************************************************
  API NetDisconnect: disconnect nodes from all other nodes
    * unlike NetDelConn, no partition is created
 ***************************************************************************)
NetDisconnect(nodes) ==
    LET res == NetDelConn(nodes)
    IN [res EXCEPT ![1] = [conn |-> _netman.conn] @@ @]

(***************************************************************************
  API NetPartConn: add a network partition
 ***************************************************************************)
_NetPartConnFlush(nodes, conn, inc) ==
    LET msgs == _FlushMsgs(nodes, _msgs)
        msgs_sum == _WireSum(msgs)
    IN <<conn @@ msgs_sum @@ _NetIncHelper(inc), msgs, <<"conn_part_flush", nodes>>>>

NetPartConn(nodes) ==
    LET conn == [ conn |-> _PartConn(nodes, _netman.conn) ]
    IN IF FLUSH_DISCONN
       THEN _NetPartConnFlush(nodes, conn, "n_part")
       ELSE <<conn @@ NetIncPart, _msgs, <<"conn_part", nodes>>>>

(***************************************************************************
  API NetDisconnect: disconnect nodes from all others except in nodes
    * unlike NetDisconnect, inter-nodes connections are not flushed
 ***************************************************************************)
NetDisconnectOthers(nodes) ==
    LET res == NetPartConn(nodes)
    IN [res EXCEPT ![1] = [conn |-> _netman.conn] @@ @]

(***************************************************************************
  API NetCureConn: connect all nodes
 ***************************************************************************)
NetCureConn == <<[ conn |-> <<_GetNodes>> ] @@ NetIncCure, _msgs, <<"conn_cure">>>>

(***************************************************************************
  API NetIsConn: check s0 and s1 are connected
 ***************************************************************************)
NetIsConn(s0, s1) ==
    Len(SelectSeq(_netman.conn, LAMBDA p: {s0, s1} \subseteq p)) /= 0

(***************************************************************************
  API NetIsParted: check if network is partitioned
 ***************************************************************************)
NetIsParted ==
    IF \/ Len(_netman.conn) /= 1
       \/ _netman.conn[1] /= _GetNodes
    THEN TRUE
    ELSE FALSE

---- \* Network send and recv functions

(***************************************************************************
  _AddMsg: add msg m to msgs
    * return <<added count, updated msgs>>
 ***************************************************************************)
_AddMsg(m, msgs) ==
    LET src == m.src
        dst == m.dst
    IN IF NetIsConn(src, dst) THEN <<1, [ msgs EXCEPT ![src][dst] = Append(@, m) ]>>
       ELSE <<0, msgs>>  \* dropped

_AddSrcDstMsg(src, dst, m, msgs) ==
    _AddMsg([src |-> src, dst |-> dst] @@ m, msgs)

(***************************************************************************
  _BatchAddMsgs: batch add multi messages to msgs
    * return <<added count, updated msgs>>
 ***************************************************************************)
_BatchAddMsgs(ms, msgs) ==
    LET F[i \in 0..Len(ms)] ==
        IF i = 0 THEN <<0, msgs, <<"msg_batch_add">>>>
        ELSE LET m == ms[i]
                 res == _AddMsg(m, F[i-1][2])
             IN <<res[1]+F[i-1][1], res[2], Append(F[i-1][3],
                  IF res[1] = 1 THEN <<"ok", m.src, m.dst>>
                  ELSE <<"dropped", m.src, m.dst>>)>>
    IN F[Len(ms)]

_BatchAddMsgDsts(src, dsts_, m_, msgs) ==
    LET dsts == SetToSeq(dsts_)
        n_servers == Len(dsts)
        F[i \in 0..n_servers] ==
        IF i = 0 THEN <<0, msgs, <<"msg_batch_add">>>>
        ELSE LET dst == dsts[i]
                 m == [src |-> src, dst |-> dst] @@ m_
                 res == _AddMsg(m, F[i-1][2])
             IN <<res[1]+F[i-1][1], res[2], Append(F[i-1][3],
                  IF res[1] = 1 THEN <<"ok", m.src, m.dst>>
                  ELSE <<"dropped", m.src, m.dst>>)>>
    IN F[n_servers]

_BatchAddDstMsgs(src, dst, ms, msgs) ==
    IF NetIsConn(src, dst)
    THEN <<Len(ms), [ msgs EXCEPT ![src][dst] = @ \o ms ], <<"msg_batch_add_ok", src, dst>>>>
    ELSE <<0, msgs, <<"msg_batch_add_dropped", src, dst>>>>

(***************************************************************************
  _DelMsg: delete m from msgs return <<deleted count, updated msgs>>
 ***************************************************************************)
_DelMsg(m, msgs) ==
    <<1, [ msgs EXCEPT ![m.src][m.dst] = Tail(@)]>>

_DelSrcDstMsg(src, dst, msgs) ==
    <<1, [ msgs EXCEPT ![src][dst] = Tail(@)]>>

(***************************************************************************
  _BatchDelMsg: batch delete multi messages of msgs
    * return <<delete count, updated msgs>>
 ***************************************************************************)
_BatchDelMsg(ms, msgs) ==
    LET F[i \in 0..Len(ms)] ==
        IF i = 0 THEN <<0, msgs, <<"msg_batch_del">>>>
        ELSE LET m == ms[i]
                 res == _DelMsg(m, F[i-1][2])
             IN <<res[1]+F[i-1][1], res[2], Append(F[i-1][3],
                  <<"ok", m.dst, m.src>>) >>
    IN F[Len(ms)]

(***************************************************************************
  _GetMsg: get m from msgs[src][dst]
    * since it is fifo network, only head msg can be obtained
 ***************************************************************************)
_GetMsg(src, dst, msgs) ==
    LET m_ == msgs[src][dst]
        len == Len(m_)
    IN IF len > 0
       THEN IF "src" \in DOMAIN m_[1]
            THEN m_[1]
            ELSE [ src |-> src, dst |-> dst ] @@ m_[1]
       ELSE NULL_MSG

(***************************************************************************
  _ReplyMsg: delete request from msgs and then add reponse to msgs
    * return <<decreased wire msgs count, msgs>>
 ***************************************************************************)
_ReplyMsg(reponse, request, msgs) ==
    LET del == _DelMsg(request, msgs)
        add == _AddMsg(reponse, del[2])
    IN [add EXCEPT ![1] = del[1]-@]
    \* IN <<del[1]-add[1], add[2]>>

_ReplySrcDstMsg(src, dst, m, msgs) ==
    LET del == _DelSrcDstMsg(dst, src, msgs)
        add == _AddSrcDstMsg(src, dst, m, del[2])
    IN [add EXCEPT ![1] = del[1]-@]
    \* IN <<del[1]-add[1], add[2]>>

(***************************************************************************
  API NetGetMsg: Get msg from src -> dst FIFO head
    * return msg m
 ***************************************************************************)
NetGetMsg(src, dst) == _GetMsg(src, dst, _msgs)

(***************************************************************************
  API NetDelMsg, NetDelSrcDstMsg: Del first msg of m.src -> m.dst
    * return <<netman, msg, cmd>>
    * update with NetUpdate
 ***************************************************************************)
NetDelMsg(m) ==
    LET res == _DelMsg(m, _msgs)
    IN <<NetDecWire @@ NetIncRecv, res[2], <<"msg_del", m.dst, m.src>>>>

NetDelSrcDstMsg(src, dst) ==
    LET res == _DelSrcDstMsg(src, dst, _msgs)
    IN <<NetDecWire @@ NetIncRecv, res[2], <<"msg_del", dst, src>>>>

NetTryDelSrcDstMsg(src, dst) ==
    IF Len(_msgs[src][dst]) = 0 THEN <<<<>>, _msgs, <<"msg_del_try", dst, src>>>>
    ELSE NetDelSrcDstMsg(src, dst)
(***************************************************************************
  API NetAddMsgSrcDst, NetAddMsg: Add m to the end of m.src -> m.dst
    * return <<netman, msg, cmd>>
 ***************************************************************************)
NetAddMsg(m) ==
    LET src == m.src
        dst == m.dst
        res == _AddMsg(m, _msgs)
    IN IF res[1] = 1
       THEN <<NetIncWire @@ NetIncSent, res[2], <<"msg_add", src, dst>>>>
       ELSE <<_netman, res[2], <<"msg_add_dropped", src, dst>>>>

NetAddSrcDstMsg(src, dst, m) ==
    NetAddMsg([src |-> src, dst |-> dst] @@ m)

(***************************************************************************
  API NetReplyMsg: delete request and try to add response to network
    * return <<netman, msg, cmd>>
 ***************************************************************************)
NetReplyMsg(response, request) ==
    LET resp == IF "src" \in DOMAIN response THEN response
                ELSE [src |-> request.dst, dst |-> request.src] @@ response
        res == _ReplyMsg(resp, request, _msgs)
    IN IF res[1] = 0
       THEN <<NetIncSent @@ NetIncRecv, res[2],
              <<"msg_reply", request.dst, request.src>>>>
       ELSE <<NetDecWire @@ NetIncRecv, res[2],
              <<"msg_reply_dropped", request.dst, request.src>>>>

NetReplySrcDstMsg(src, dst, m) ==
    LET res == _ReplySrcDstMsg(src, dst, m, _msgs)
    IN IF res[1] = 0
       THEN <<NetIncSent @@ NetIncRecv, res[2],
              <<"msg_reply", src, dst>>>>
       ELSE <<NetDecWire @@ NetIncRecv, res[2],
              <<"msg_reply_dropped", src, dst>>>>

(***************************************************************************
  API NetBatchAddMsg: batch add messages ms to msgs
 ***************************************************************************)
NetBatchAddMsg(ms) ==
    LET res == _BatchAddMsgs(ms, _msgs)
    IN [res EXCEPT ![1] = NetIncBy("n_sent", res[1]) @@ NetIncBy("n_wire", res[1])]
    \* IN <<NetIncBy("n_sent", res[1]) @@ NetIncBy("n_wire", res[1]), res[2], res[3]>>

NetBatchAddDstMsgs(src, dst, ms) ==
    LET res == _BatchAddDstMsgs(src, dst, ms, _msgs)
    IN [res EXCEPT ![1] = NetIncBy("n_sent", res[1]) @@ NetIncBy("n_wire", res[1])]
    \* IN <<NetIncBy("n_sent", res[1]) @@ NetIncBy("n_wire", res[1]), res[2], res[3]>>

(***************************************************************************
  API NetBatchAddMsgDsts: batch add a message m from src to all dsts
 ***************************************************************************)
NetBatchAddMsgDsts(src, dsts, m) ==
    LET res == _BatchAddMsgDsts(src, dsts, m, _msgs)
    IN [res EXCEPT ![1] = NetIncBy("n_sent", res[1]) @@ NetIncBy("n_wire", res[1])]
    \* IN <<NetIncBy("n_sent", res[1]) @@ NetIncBy("n_wire", res[1]), res[2], res[3]>>

(***************************************************************************
  API NetReplyBatchAddMsg: remove request and batch add ms to msgs
 ***************************************************************************)
NetReplyBatchAddMsg(ms, request) ==
    LET del == _DelMsg(request, _msgs)
        add == _BatchAddMsgs(ms, del[2])
    IN <<NetIncBy("n_sent", add[1]) @@ NetIncBy("n_wire", add[1]-del[1]) @@ NetIncRecv,
        add[2], Append(<<"msg_batch_add_reply", request.dst, request.src>>, add[3])>>

NetReplyBatchAddDstMsgs(src, dst, ms) ==
    LET del == _DelSrcDstMsg(dst, src, _msgs)
        add == _BatchAddDstMsgs(src, dst, ms, del[2])
    IN <<NetIncBy("n_sent", add[1]) @@ NetIncBy("n_wire", add[1]-del[1]) @@ NetIncRecv,
        add[2], Append(<<"msg_batch_add_reply", src, dst>>, add[3])>>

NetReplyBatchAddMsgDsts(src, request_sender, dsts, m) ==
    LET del == _DelSrcDstMsg(request_sender, src, _msgs)
        add == _BatchAddMsgDsts(src, dsts, m, del[2])
    IN <<NetIncBy("n_sent", add[1]) @@ NetIncBy("n_wire", add[1]-del[1]) @@ NetIncRecv,
        add[2], Append(<<"msg_batch_add_reply", src, request_sender>>, add[3])>>

(***************************************************************************
  API NetBatchDeleteBatchAddMsg: batch remove requests and batch add ms to msgs
 ***************************************************************************)
NetBatchDeleteBatchAddMsg(ms, to_deletes) ==
    LET del == _BatchDelMsg(to_deletes, _msgs)
        add == _BatchAddMsgs(ms, del[2])
    IN <<NetIncBy("n_sent", add[1]) @@ NetIncBy("n_wire", add[1]-del[1]) @@ NetIncBy("n_recv", del[1]),
        add[2], Append(<<"msg_batch_delete_add">>, del[3] \o add[3])>>

(***************************************************************************
  API NetBatchDeleteMsg: batch remove messages
 ***************************************************************************)
NetBatchDeleteMsg(to_deletes) ==
    LET del == _BatchDelMsg(to_deletes, _msgs)
    IN <<NetDecBy("n_wire", del[1]) @@ NetIncBy("n_recv", del[1]),
        del[2], Append(<<"msg_batch_delete">>, del[3])>>

(***************************************************************************
  API NetNoAction: Network state unchanged
    * return <<netman, msg>>
 ***************************************************************************)
NetNoAction(cmd) == <<_netman, _msgs, <<cmd>>>>
NetNoActionInc(cmd, inc) == <<_NetIncHelper(inc) @@ _netman, _msgs, <<cmd>>>>
NetArg(arg, args) == [args EXCEPT ![1] = arg @@ @]
NetNoActionArgCmd(arg, cmd) == NetArg(arg, NetNoAction(cmd))

=============================================================================
\* Modification History
\* Last modified Sat Aug 05 19:44:02 CST 2023 by tangruize
\* Last modified Wed Aug 02 13:32:50 CST 2023 by tangr
\* Last modified Mon Jul 31 14:02:48 CST 2023 by tangr
\* Created Fri Apr 22 17:27:57 CST 2022 by tangruize

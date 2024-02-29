----------------- MODULE UdpNetwork ----------------------
EXTENDS TLC, Naturals, FiniteSets, Sequences
(***************************************************************************
  VARIABLES definitions: see InitUdpNetwork
 ***************************************************************************)

VARIABLES _msgs,    \* Messages in the network
          _netman,  \* Network manager
          _netcmd   \* Current network cmd


(* NULL_MSG: represent a null msg in some condition checkings 
    shoule be a model value if its type is constant *)
CONSTANT NULL_MSG
\*NULL_MSG == [ NULL_MSG |-> "" ]

---- \* Common functions

(*****)
(*  API InitUdpNetwork(nodes):
    - _msgs: init to empty sequences of [src][dst] records
        * format [seq |-> 0, src |-> s0, dst |-> s1, type |-> sth, data -> sth]
        * src and dst will be dropped when storing in _msgs
        * type and data are user defined fields
    _ _netman:
        - n_sent: number of msgs sent to network, to indicate next msg seq
        - n_recv: number of msgs delivered to server 
        - n_wire: number of msgs in network but not delivered yet
        
    - _netcmd: <<"Init">> *)
(*****)


InitUdpNetworkNetman(nodes, cmd, additonalNetman) ==
    /\ _msgs = {}
    /\ _netman = additonalNetman @@ 
                  [ n_sent |-> 0, n_recv |-> 0, n_wire |-> 0]
    /\ _netcmd = <<cmd>>

InitUdpNetwork(nodes) == InitUdpNetworkNetman(nodes, "init", <<>>)

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

------ \* Update _netman functions

(***************************************************************************
  _NetGetHelper and _NetIncHelper: get, inc and dec member of _netman records
 ***************************************************************************)
_NetGetHelper(member) == _netman[member]
_NetIncHelper(member) == (member :> _netman[member] + 1)
_NetDecHelper(member) == (member :> _netman[member] - 1)
NetIncBy(member, number) == (member :> _netman[member] + number)

NetGetSent == _NetGetHelper("n_sent")
NetIncSent == _NetIncHelper("n_sent")
NetGetRecv == _NetGetHelper("n_recv")
NetIncRecv == _NetIncHelper("n_recv")
NetGetWire == _NetGetHelper("n_wire")
NetIncWire == _NetIncHelper("n_wire")
NetDecWire == _NetDecHelper("n_wire")



---- \* Network send and recv functions


\* _AddMsgSrcDstSeq(src, dst, seq, m, msgs) == 
\*     LET m_ == [x \in ((DOMAIN m \union {"seq"}) \ {"src", "dst"}) |-> 
\*                 IF x = "seq" THEN seq ELSE m[x]]
\*     IN <<1, [ msgs EXCEPT ![src][dst] = Append(@, m_)]>>

\* _AddMsgSrcDst(src, dst, m, msgs) == 
\*     LET seq == NetGetSent + 1
\*     IN _AddMsgSrcDstSeq(src, dst, seq, m, msgs)

\* _AddMsg(m, msgs) == _AddMsgSrcDst(m.src, m.dst, m, msgs)


(* _AddMsgSeq, _AddMsg : add msg m to msgs 
    return << added count, updated msgs >>
    set global seq to msg m *)

(****)
(* API updater : 
    * return <<netman, msg, cmd>>  *)
(****)
NetmanIncField(field, updater) ==
    <<_NetIncHelper(field) @@ updater[1]>> @@ updater 


\*NetmanIncFieldWithoutUpdate(field) ==
\*    <<_NetIncHelper(field) , _msgs ,_netcmd>>


\* return <<added count, updated msgs>>
_AddMsgSeq(m, seq, msgs) == LET m_ ==    IF "seq" \in DOMAIN m  \* TODO: add partition, see wraft
                                THEN {[ m EXCEPT !["seq"] = seq ]}
                                ELSE {m @@ ( "seq" :> seq )}
                            IN <<1, msgs \union m_>>

\* Add msg to msgs, increase scr.nMessage.
_AddMsg(m, msgs) == LET seq == NetGetSent + 1  
                   IN _AddMsgSeq(m, seq, msgs)



(****)
(* _BatchAddMsgs: batch add multi messages to msgs
    * return <<added count, updated msgs>>
    * set global seq to each msg m 
*)
(****)
_BatchAddmsgs(ms, msgs)==
    LET F[i \in 0 .. Len(ms)] ==
        IF i = 0 THEN <<0, msgs, <<"msg_batch_add">> >>
        ELSE LET m == ms[i]
                 seq == NetGetSent + F[i-1][1] + 1
                 res == _AddMsgSeq(m, seq ,F[i-1][2])
             IN << res[1] + F[i-1][1], res[2], Append(F[i-1][3],
                    IF res[1] = 1 THEN <<"ok", seq, m.src, m.dst>>
                    ELSE <<"dropped", seq, m.src, m.dst>>) >>
    IN F[Len(ms)]


(***************************************************************************
  _DelMsg: delete m from msgs return <<deleted count, updated msgs>>
 ***************************************************************************)
\* Del msg from msgs.
_DelMsg(m, msgs) == IF m \in msgs THEN <<1, msgs\ {m}>>  ELSE Assert(FALSE, "Delmsg: not in network")

(***************************************************************************
  _ReplyMsg: delete request from msgs and then add reponse to msgs
    * return <<decreased wire msgs count, msgs>>
 ***************************************************************************)
\* Combination of Send and Discard.
_ReplyMsg(response, request, msgs) ==
    LET del == _DelMsg(request, msgs)
        add == _AddMsg(response, del[2])
    IN <<del[1] - add[1], add[2]>>

(***************************************************************************
  API NetGetMsg: Get msg from src -> dst FIFO head
    * return msg m
    真的需要实现吗？？ 讨论
 ***************************************************************************)
\* NetGetMsg(src, dst) == _GetMsg(src, dst, _msgs)


(***************************************************************************
  API NetDelMsg: Del msgs of m
    * return <<netman, msgs, cmd>>
    * update with NetUpdate
 ***************************************************************************)
NetDelMsg(m) == 
    LET res == _DelMsg(m, _msgs)
    IN <<NetDecWire @@ NetIncRecv, res[2], <<"msg_del", m.seq, m.src, m.dst>> >>  \* 为什么要增加inc recv？模拟发送过去了吗


(***************************************************************************
  API NetDropMsg: Drop msgs of m
    * return <<netman, msgs, cmd>>
    * update with NetUpdate
 ***************************************************************************)
NetDropMsg(m) == 
    LET res == _DelMsg(m, _msgs)
    IN <<NetDecWire , res[2], <<"msg_drop", m.seq, m.src, m.dst>> >>  \* 为什么要增加inc recv？模拟发送过去了吗



(***************************************************************************
  API NetDupMsg: Duplicate msgs of m
    * return <<netman, msgs, cmd>>
    * update with NetUpdate
 ***************************************************************************)
NetDupMsg(m) == 
    LET res == _AddMsg(m, _msgs)
    IN <<NetIncSent @@ NetIncWire , res[2], <<"msg_dup", m.seq, m.src, m.dst>> >>  \* 为什么要增加inc recv？模拟发送过去了吗


(****)
(* API NetAddMsg : add m into msgs
    * return <<netman, msg, cmd>>  *)
(****)
NetAddMsg(m) == 
    LET res == _AddMsg(m, _msgs)
    IN IF res[1] = 1
       THEN <<NetIncSent @@ NetIncWire, res[2], <<"msg_add",  m.src, m.dst>> >>  \* here we do not need seq, because we put in network then sort
       ELSE <<_netman, res[2], <<"msg_add_dropped",  m.src, m.dst>> >>

NetReplyMsg(response, request) ==
    LET res == _ReplyMsg(response, request, _msgs)
    IN  IF res[1] = 0
        THEN <<NetIncSent @@ NetIncRecv, res[2], 
                << "msg_reply", request.seq , request.src, request.dst>> >>
        ELSE <<NetDecWire @@ NetIncRecv, res[2],
                <<"msg_reply_dropped", request.seq, request.src, request.dst>> >>


(***************************************************************************
  API NetBatchAddMsg: batch add messages ms to msgs
 ***************************************************************************)
NetBatchAddMsg(ms) == 
    LET res == _BatchAddmsgs(ms, _msgs)
    IN <<NetIncBy("n_sent", res[1]) @@ NetIncBy("n_wire", res[1]), res[2], res[3]>>

(***************************************************************************
  API NetNoAction: Network state unchanged
    * return <<netman, msg>>
 ***************************************************************************)
NetNoAction(cmd) == <<_netman, _msgs, cmd>>


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


====
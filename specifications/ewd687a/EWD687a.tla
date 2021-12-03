------------------------------ MODULE EWD687a ------------------------------
EXTENDS Integers, TLC

CONSTANTS Procs, Leader, Edges

ASSUME /\ Leader \in Procs
       /\ \A e \in Edges : (e \in Procs \X Procs) /\ (e[1] # e[2])
       /\ \A e \in Edges : e[2] # Leader

InEdges(p)  == {e \in Edges : e[2] = p}
OutEdges(p) == {e \in Edges : e[1] = p}
NotAnEdge  == << >>
\* NotAProc == CHOOSE p : p \notin Procs

VARIABLES active, msgs, acks, sentUnacked, rcvdUnacked, upEdge 
vars == <<active, msgs, acks, sentUnacked, rcvdUnacked, upEdge>>

neutral(p) == /\ ~ active[p]
              /\ \A e \in InEdges(p) : rcvdUnacked[e] = 0
              /\ \A e \in OutEdges(p) : sentUnacked[e] = 0
              
              
TypeOK == /\ active \in [Procs -> BOOLEAN]
          /\ msgs \in [Edges -> Nat]
          /\ acks \in [Edges -> Nat]
          /\ sentUnacked \in [Edges -> Nat]
          /\ rcvdUnacked \in [Edges -> Nat]
          /\ upEdge \in [Procs \ {Leader} -> Edges \cup {NotAnEdge}]
          /\ \A p \in Procs \ {Leader} :  upEdge[p] # NotAnEdge => upEdge[p][2] = p
 
Init == /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
        /\ msgs = [e \in Edges |-> 0]
        /\ acks = [e \in Edges |-> 0]
        /\ sentUnacked = [e \in Edges |-> 0]
        /\ rcvdUnacked = [e \in Edges |-> 0]
        /\ upEdge = [p \in Procs \ {Leader} |-> NotAnEdge]  \* The initial value doesn't matter

SendMsg(p) == /\ active[p]
              /\ \E e \in OutEdges(p) : 
                     /\ sentUnacked' = [sentUnacked EXCEPT ![e] = @ + 1] 
                     /\ msgs' = [msgs EXCEPT ![e] = @ + 1]
              /\ UNCHANGED <<active, acks, rcvdUnacked, upEdge>>

SendAck(p) == /\ \E e \in InEdges(p) : 
                     /\ rcvdUnacked[e] > 0
                     /\ (e = upEdge[p] ) =>
                        \/ rcvdUnacked[e] > 1
                        \/ e # upEdge[p]
                        \/ /\ \A d \in OutEdges(p) : sentUnacked[d] = 0
                           /\ \A d \in InEdges(p) \ {e} : rcvdUnacked[d] = 0
                           /\ ~active[p] 
                     /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ - 1] 
                     /\ acks' = [acks EXCEPT ![e] = @ + 1]
              /\ UNCHANGED <<active, msgs, sentUnacked, upEdge>>
 
 RcvMsg(p) == \E e \in InEdges(p) : 
                  /\ msgs[e] > 0  
                  /\ msgs' = [msgs EXCEPT ![e] = @ - 1]  
                  /\ rcvdUnacked' = [rcvdUnacked EXCEPT ![e] = @ + 1]
                  /\ active' = [active EXCEPT ![p] = TRUE]
                  /\ upEdge' = IF neutral(p) THEN [upEdge EXCEPT ![p] = e]
                                             ELSE upEdge
                  /\ UNCHANGED <<acks, sentUnacked>>
\*                  /\ Assert(FALSE,FALSE)
                  
 RcvAck(p) == \E e \in OutEdges(p) :
                  /\ acks[e] > 0
                  /\ acks' = [acks EXCEPT ![e] = @ - 1]
                  /\ sentUnacked' = [sentUnacked EXCEPT ![e] = @ - 1]
                  /\ UNCHANGED <<active, msgs, rcvdUnacked, upEdge>>
 
 Idle(p) == /\ active' = [active EXCEPT ![p] = FALSE]
            /\ UNCHANGED <<msgs, acks, sentUnacked, rcvdUnacked, upEdge>>
            
 Next == \E p \in Procs : SendMsg(p) \/ SendAck(p) \/ RcvMsg(p) \/ RcvAck(p)
                             \/ Idle(p)
                             
 Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
 
 --------------
 DT1Inv == neutral(Leader) => \A p \in Procs \ {Leader} : neutral(p)
 
 Terminated == /\ \A p \in Procs : ~active[p]
               /\ \A e \in Edges : msgs[e] = 0
 DT2 == Terminated ~> neutral(Leader) 
=============================================================================
\* Modification History
\* Last modified Fri Oct 01 12:51:49 PDT 2021 by lamport
\* Created Wed Sep 29 01:36:40 PDT 2021 by lamport

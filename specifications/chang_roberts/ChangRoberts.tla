---------------------------- MODULE ChangRoberts ----------------------------
(***************************************************************************)
(* Algorithm by Chang and Roberts for electing a leader on a               *)
(* unidirectional ring. The algorithm originally appeared as               *)
(* E. Chang, R. Roberts: An improved algorithm for decentralized           *)
(* extrema-finding in circular configurations of processes,                *)
(* CACM 22(5): 281-283, 1979.                                              *)
(***************************************************************************)
EXTENDS Naturals

(***************************************************************************)
(* Constant parameters:                                                    *)
(* - N is the number of nodes                                              *)
(* - Id(i) denotes the identity of node i                                  *)
(*   The algorithm can be initiated by several nodes, and the node with    *)
(*   the smallest identity will be elected as the leader.                  *)
(***************************************************************************)
CONSTANTS N, Id(_)

Node == 1 .. N

ASSUME
  /\ N \in Nat \ {0}
  /\ \A n \in Node : Id(n) \in Nat
  /\ \A m,n \in Node : Id(m) = Id(n) => m = n  \* IDs are unique

next(n) == IF n=N THEN 1 ELSE n+1  \* successor along the ring

(** Chang-Roberts algorithm written in PlusCal
--algorithm ChangRoberts {
  (* msgs[n]: messages waiting to be received by node n *)
  variable msgs = [n \in Node |-> {}];
  fair process (node \in Node)
     variables
       (* is this node an initiator: assigned non-deterministically *)
       initiator \in BOOLEAN,
       state = IF initiator THEN "cand" ELSE "lost"; {
   n0: if (initiator) {
          \* send own ID to neighbor
          msgs[next(self)] := @ \cup {Id(self)};
   n1:    while (state # "won") {
             \* handle some waiting message
             with (q \in msgs[self]) {
                if (q < Id(self)) { \* received message for smalled ID: pass it on, record loss
                   state := "lost";
                   msgs := [msgs EXCEPT ![self] = @ \ {q}, 
                                        ![next(self)] = @ \cup {q}];
                }
                else { \* don't pass on other messages
                   msgs := [msgs EXCEPT ![self] = @ \ {q}];
                   \* the process wins the election if it receives its own ID
                   if (q = Id(self)) { state := "won"; }
                }
             } \* end with
          } \* end while
       } else { \* non-initiator: pass all messages to the neighbor
   n2:    while (TRUE) {
             with (q \in msgs[self]) {
                msgs := [msgs EXCEPT ![self] = @ \ {q},
                                     ![next(self)] = @ \cup {q}];
             } \* end with
          } \* end while
       } \* end if
   } \* end process
}  \* end algorithm
**)
\* BEGIN TRANSLATION
VARIABLES msgs, pc, initiator, state

vars == << msgs, pc, initiator, state >>

ProcSet == (Node)

Init == (* Global variables *)
        /\ msgs = [n \in Node |-> {}]
        (* Process node *)
        /\ initiator \in [Node -> BOOLEAN]
        /\ state = [self \in Node |-> IF initiator[self] THEN "cand" ELSE "lost"]
        /\ pc = [self \in ProcSet |-> "n0"]

n0(self) == /\ pc[self] = "n0"
            /\ IF initiator[self]
                  THEN /\ msgs' = [msgs EXCEPT ![next(self)] = @ \cup {Id(self)}]
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "n2"]
                       /\ msgs' = msgs
            /\ UNCHANGED << initiator, state >>

n1(self) == /\ pc[self] = "n1"
            /\ IF state[self] # "won"
                  THEN /\ \E q \in msgs[self]:
                            IF q < Id(self)
                               THEN /\ state' = [state EXCEPT ![self] = "lost"]
                                    /\ msgs' = [msgs EXCEPT ![self] = @ \ {q},
                                                            ![next(self)] = @ \cup {q}]
                               ELSE /\ msgs' = [msgs EXCEPT ![self] = @ \ {q}]
                                    /\ IF q = Id(self)
                                          THEN /\ state' = [state EXCEPT ![self] = "won"]
                                          ELSE /\ TRUE
                                               /\ state' = state
                       /\ pc' = [pc EXCEPT ![self] = "n1"]
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << msgs, state >>
            /\ UNCHANGED initiator

n2(self) == /\ pc[self] = "n2"
            /\ \E q \in msgs[self]:
                 msgs' = [msgs EXCEPT ![self] = @ \ {q},
                                      ![next(self)] = @ \cup {q}]
            /\ pc' = [pc EXCEPT ![self] = "n2"]
            /\ UNCHANGED << initiator, state >>

node(self) == n0(self) \/ n1(self) \/ n2(self)

Next == (\E self \in Node: node(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Node : WF_vars(node(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
-----------------------------------------------------------------------------
(* type correctness *)
TypeOK ==
  /\ pc \in [Node -> {"n0", "n1", "n2", "Done"}]
  /\ msgs \in [Node -> SUBSET {Id(n) : n \in Node}]
  /\ initiator \in [Node -> BOOLEAN]
  /\ state \in [Node -> {"cand", "lost", "won"}]

(***************************************************************************)
(* Safety property: when node n wins the election, it is the initiator     *)
(* with the smallest ID, and all other nodes know that they lost.          *)
(***************************************************************************)
Correctness ==
  \A n \in Node : state[n] = "won" =>
     /\ initiator[n]
     /\ \A m \in Node \ {n} : 
           /\ state[m] = "lost"
           /\ initiator[m] => Id(m) > Id(n)

(***************************************************************************)
(* Liveness property: if there is an initiator then eventually there       *)
(* will be a winner.                                                       *)
(***************************************************************************)
Liveness ==
  (\E n \in Node : initiator[n]) ~> (\E n \in Node : state[n] = "won")

=============================================================================
\* Modification History
\* Last modified Sun Jun 12 18:33:42 CEST 2016 by merz
\* Created Sat Apr 23 14:05:31 CEST 2016 by merz

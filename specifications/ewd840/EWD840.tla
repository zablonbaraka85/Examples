------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* TLA+ specification of an algorithm for distributed termination          *)
(* detection on a ring, due to Dijkstra, published as EWD 840:             *)
(* Derivation of a termination detection algorithm for distributed         *)
(* computations (with W.H.J.Feijen and A.J.M. van Gasteren).               *)
(***************************************************************************)
EXTENDS Naturals, TLAPS

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]    \* status of nodes (active or passive)
  /\ color \in [Nodes -> Color]       \* color of nodes
  /\ tpos \in Nodes                   \* token position
  /\ tcolor \in Color                 \* token color

(* Initially the token is black. The other variables may take
   any "type-correct" values. *)
Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor = "black"

(* Node 0 may initiate a probe when it has the token and
   when either it is black or the token is black. It passes
   a white token to node N-1 and paints itself white. *)
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

(* A node i different from 0 that possesses the token may pass
   it to node i-1 under the following circumstances:
   - node i is inactive or
   - node i is colored black or
   - the token is black.
   Note that the last two conditions will result in an
   inconclusive round, since the token will be black.
   The token will be stained if node i is black, otherwise 
   its color is unchanged. Node i will be made white. *)
PassToken(i) == 
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

(* token passing actions controlled by the termination detection algorithm *)
System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

(* An active node i may activate another node j by sending it
   a message. If j>i (hence activation goes against the direction
   of the token being passed), then node i becomes black. *)
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j>i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

(* Any active node may become inactive at any moment. *)
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

(* actions performed by the underlying algorithm *)
Environment == \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

(* next-state relation: disjunction of above actions *)
Next == System \/ Environment

vars == <<active, color, tpos, tcolor>>

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

(***************************************************************************)
(* Non-properties, useful for validating the specification with TLC.       *)
(***************************************************************************)
TokenAlwaysBlack == tcolor = "black"

NeverChangeColor == [][ UNCHANGED color ]_vars

(***************************************************************************)
(* Main safety property: if there is a white token at node 0 then every    *)
(* node is inactive.                                                       *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

(***************************************************************************)
(* Liveness property: termination is eventually detected.                  *)
(***************************************************************************)
Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* The following property asserts that when every process always           *)
(* eventually terminates then eventually termination will be detected.     *)
(* It does not hold since processes can wake up each other.                *)
(***************************************************************************)
FalseLiveness ==
  (\A i \in Nodes : []<> ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* The following property says that eventually all nodes will terminate    *)
(* assuming that from some point onwards no messages are sent. It is       *)
(* not supposed to hold: any node may indefinitely perform local           *)
(* computations. However, this property is verified if the fairness        *)
(* condition WF_vars(Next) is used instead of only WF_vars(System) that    *)
(* requires fairness of the actions controlled by termination detection.   *)
(***************************************************************************)
SpecWFNext == Init /\ [][Next]_vars /\ WF_vars(Next)
AllNodesTerminateIfNoMessages ==
  <>[][\A i \in Nodes : ~ SendMsg(i)]_vars => <>(\A i \in Nodes : ~ active[i])

(***************************************************************************)
(* Dijkstra's inductive invariant                                          *)
(***************************************************************************)
Inv == 
  \/ P0:: \A i \in Nodes : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

(***************************************************************************)
(* Use the following specification to check that the predicate             *)
(* TypeOK /\ Inv is inductive for EWD 840: verify that it is an            *)
(* (ordinary) invariant of a specification obtained by replacing the       *)
(* initial condition by that conjunction.                                  *)
(***************************************************************************)
CheckInductiveSpec == TypeOK /\ Inv /\ [][Next]_vars
-----------------------------------------------------------------------------
(***************************************************************************)
(* Interactive proof of safety using TLAPS.                                *)
(***************************************************************************)

(***************************************************************************)
(* The algorithm is type-correct: TypeOK is an inductive invariant.        *)
(***************************************************************************)
LEMMA TypeCorrect == Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, Color
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  BY NAssumption DEF TypeOK, Color, Nodes, vars, Next, System, Environment,
                     InitiateProbe, PassToken, SendMsg, Deactivate
<1>. QED  BY <1>1, <1>2, PTL DEF Spec


(***************************************************************************)
(* Follows a more detailed proof of the same lemma. It illustrates how     *)
(* proofs can be decomposed hierarchically. Use the "Decompose Proof"      *)
(* command (C-G C-D) to prepare the skeleton of the level-2 steps.         *)
(***************************************************************************)
LEMMA Spec => []TypeOK
<1>1. Init => TypeOK
  BY DEF Init, TypeOK, Color
<1>2. TypeOK /\ [Next]_vars => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      [Next]_vars
               PROVE  TypeOK'
    OBVIOUS
  <2>. USE NAssumption DEF TypeOK, Nodes, Color
  <2>1. CASE InitiateProbe
    BY <2>1 DEF InitiateProbe
  <2>2. ASSUME NEW i \in Nodes \ {0},
               PassToken(i)
        PROVE  TypeOK'
    BY <2>2 DEF PassToken
  <2>3. ASSUME NEW i \in Nodes,
               SendMsg(i)
        PROVE  TypeOK'
    BY <2>3 DEF SendMsg
  <2>4. ASSUME NEW i \in Nodes,
               Deactivate(i)
        PROVE  TypeOK'
    BY <2>4 DEF Deactivate
  <2>5. CASE UNCHANGED vars
    BY <2>5 DEF vars
  <2>. QED
    BY <2>1, <2>2, <2>3, <2>4, <2>5 DEF Environment, Next, System
<1>. QED  BY <1>1, <1>2, PTL DEF Spec

(***************************************************************************)
(* Prove the main soundness property of the algorithm by (1) proving that  *)
(* Inv is an inductive invariant and (2) that it implies correctness.      *)
(***************************************************************************)
THEOREM Safety == Spec => []TerminationDetection
<1>1. Init => Inv
  BY NAssumption DEF Init, Inv, Nodes
<1>2. TypeOK /\ Inv /\ [Next]_vars => Inv'
  BY NAssumption
     DEF TypeOK, Inv, Next, vars, Nodes, Color,
         System, Environment, InitiateProbe, PassToken, SendMsg, Deactivate
<1>3. Inv => TerminationDetection
  BY NAssumption DEF Inv, TerminationDetection, terminationDetected, Nodes
<1>. QED
  BY <1>1, <1>2, <1>3, TypeCorrect, PTL DEF Spec


(***************************************************************************)
(* Step <1>3 of the above proof shows that Dijkstra's invariant implies    *)
(* TerminationDetection. If you find that one-line proof too obscure, here *)
(* is a more detailed, hierarchical proof of that same implication.        *)
(***************************************************************************)
LEMMA Inv => TerminationDetection
<1>1. SUFFICES ASSUME tpos = 0, tcolor = "white", 
                      color[0] = "white", ~ active[0],
                      Inv
               PROVE  \A i \in Nodes : ~ active[i]
  BY <1>1 DEF TerminationDetection, terminationDetected
<1>2. ~ Inv!P2  BY tcolor = "white" DEF Inv
<1>3. ~ Inv!P1  BY <1>1 DEF Inv
<1>. QED
  <2>1. Inv!P0  BY Inv, <1>2, <1>3 DEF Inv
  <2>.  TAKE i \in Nodes
  <2>3. CASE i = 0  BY <2>1, <1>1, <2>3
  <2>4. CASE i \in 1 .. N-1
    <3>1. tpos < i  BY tpos=0, <2>4, NAssumption
    <3>2. i < N  BY NAssumption, <2>4
    <3>. QED  BY <3>1, <3>2, <2>1
  <2>. QED  BY <2>3, <2>4 DEF Nodes

=============================================================================
\* Modification History
\* Last modified Mon May 30 20:40:46 CEST 2016 by merz
\* Created Mon Sep 09 11:33:10 CEST 2013 by merz

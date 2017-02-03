------------------------------ MODULE bcastByz ------------------------------

(*
 * TLA+ encoding of a parameterized model of the broadcast distributed  
 * algorithm with Byzantine faults.
 *
 * This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:
 *
 * T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
 * simple fault-tolerant algorithms. Distributed Computing 1987,
 * Volume 2, Issue 2, pp 80-94
 *                                                           
 * A short description of the parameterized model is described in: Gmeiner,   
 * Annu, et al. "Tutorial on parameterized model checking of fault-tolerant   
 * distributed algorithms." International School on Formal Methods for the  
 * Design of Computer, Communication and Software Systems. Springer  
 * International Publishing, 2014.                   
 *
 * This specification has a TLAPS proof for property Unforgeability: if process p 
 * is correct and does not broadcast (p, m, k), then no correct process ever 
 * accepts (p, m, k). The formula InitNoBcast represents that the transmitter 
 * does not broadcast any message. So, our goal is to prove the  formula
 *      (InitNoBcast /\ [][Next]_vars) => Unforg                    
 *
 * Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
 *
 * This file is a subject to the license that is bundled
 * together with this package and can be found in the file LICENSE.
 *)


EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLE Corr           (* The correct processes *)
VARIABLE Faulty         (* The faulty processes *)
                        (* Corr and Faulty are declared as variables since we want to 
                           check all possible cases. And after the initial step, Corr
                           and Faulty are unchanged. *)
VARIABLE pc             (* the control state of each process *)
VARIABLE rcvd           (* the messages received by each process *)
VARIABLE sent           (* the messages sent by all correct processes *)
VARIABLE newMessages    (* the message received at the current step by each process *)

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N                 (* all processess, including the faulty ones    *)
ByzMsgs == { <<p, "ECHO">> : p \in Faulty }                            


M == { "ECHO" }

vars == << pc, rcvd, sent, newMessages, Corr, Faulty >>

(* Both correct and faulty processes send only <ECHO> msgs. *)
Receive(self) ==
  /\ newMessages' \in SUBSET ( sent \cup ByzMsgs )
  /\ rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages' ]
                             
(* If received an INIT message and not send <ECHO> before,    
 * then send <ECHO> to all - line 3.                                        
 * UponV1 is for the 1st ITE.
 *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* If received <ECHO> from at least T + 1 distinct processes and   
 * not sent <ECHO> before, then send <ECHO> to all. Since processes  
 * send only <ECHO> msgs, #msgs = #distinct processes from which  
 * process self received msgs. UponNonFaulty is for the 3rd ITE.
 *)         
UponNonFaulty(self) ==
  /\ pc[self] /= "SE"
  /\ Cardinality(rcvd'[self]) >= T + 1
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>
        
(* If received <ECHO> from at least N - T distinct processes 
 * and not send, <ECHO> before then accepts and sends <ECHO> to all.      
 * UponAcceptNot is for the 2nd ITE when the 1st ITE was not satisfied
 * and the 2nd ITE is satisfied.                 
 *)        
UponAcceptNotSent(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>
        
(* If received <ECHO> from at least N-T distinct processes before, accepts. 
 * UponAccept is for the 2nd ITE when the 1st ITE was satisfied. 
 *)        
UponAccept(self) ==
        /\ pc[self] = "SE"
        /\ Cardinality(rcvd'[self]) >= N - T
        /\ pc' = [pc EXCEPT ![self] = "AC"]
        /\ sent' = sent
        /\ UNCHANGED << Corr, Faulty >>

(* Possible transition steps *)                
Step(self) == 
  /\ self \in Corr
  /\ Receive(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSent(self)
     \/ UponAccept(self)
     \/ UNCHANGED << pc, sent, Corr, Faulty >>                 

Init == 
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]  (* some processes received INIT messages, some didn't *)
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc             (* at least N-F correct processes*)
  /\ Cardinality(Corr) >= N - F 
  /\ Faulty = Proc \ Corr
  /\ newMessages = {}
        
(* No process receives an INIT message. *)
InitNoBcast == 
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc             (* at least N-F correct processes*)
  /\ Cardinality(Corr) >= N - F 
  /\ Faulty = Proc \ Corr
  /\ newMessages = {}
               
               
Next == \E self \in Corr: Step(self)                    

(* Add weak fairness condition since we want to check liveness properties.  *)
(* We require that if UponV1 (UponNonFaulty, UponAcceptNotSent, UponAccept) *)
(* ever becomes forever enabled, then this step must eventually occur.      *)
Spec == Init /\ [][Next]_vars 
             /\ WF_vars(\E self \in Corr: /\ Receive(self)
                                          /\ \/ UponV1(self)
                                             \/ UponNonFaulty(self)
                                             \/ UponAcceptNotSent(self)
                                             \/ UponAccept(self))


SpecNoBcast == InitNoBcast /\ [][Next]_vars
                           /\ WF_vars(\E self \in Corr: /\ Receive(self)
                                                        /\ \/ UponV1(self)                                                           
                                                           \/ UponNonFaulty(self)
                                                           \/ UponAcceptNotSent(self)
                                                           \/ UponAccept(self))

(* 
 * V0 - the initial state where a process did not receive an INIT message
 * V1 - the initial state where a process received an INIT message
 * SE - sent the ECHO message 
 * AC - accepted            
 *) 
TypeOK == /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]          
          /\ Corr \subseteq Proc
          /\ Faulty \subseteq Proc
          /\ sent \subseteq Proc \times M
          /\ newMessages \in SUBSET ( sent \cup ByzMsgs )          
          /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

(* Constraints about the cardinalities of Faulty and Corr, their elements, 
 * and the upper bound of the set of possible Byzantine messages. 
 *)          
FCConstraints == 
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ IsFiniteSet(Corr)
  /\ IsFiniteSet(Faulty)
  /\ Corr \cup Faulty = Proc 
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T   
  /\ ByzMsgs \subseteq Proc \X M            
          
(* If no correct process do not broadcast <ECHO> then no correct processes  *)  
(* accepts.                                                                 *)
UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] /= "AC")

(* The special case of the unforgeability property. When our algorithms start 
 * with InitNoBcast, we can rewrite UnforgLtl as a first-order formula.    
 *)          
Unforg == (\A i \in Proc: i \in Corr => (pc[i] /= "AC")) 


(* If a correct process broadcasts, then every correct process accepts.     *)
CorrLtl == (\A i \in Corr: pc[i] = "V1") => <>(\E i \in Corr: pc[i] = "AC")

(* If a correct process accepts, then every other correct process accepts.  *)
RelayLtl == []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))

(* It is the indutive invariant for the property Unforgeability which is used
 * by TLC to generate initial states. This inductive invariant is equivalent 
 * to IndInv_Unforg. The reasons why we use two inductive are
 *  1/ I started with TypeOK and tried to add new constraints in order to have
 *     an inductive invariant. I think it is the nature way to find an inductive
 *     invariant. Moreover, writing a TLAPS proof for IndInv_Unforg is easy 
 *     to organize and decompose.
 *  2/ However, checking IndInv_Unforg with TLC is inefficient because TLC
 *     generates too many unnecessary initial states. When TLC evaluates the
 *     expression pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ], it will generate
 *     all possible states. Too many. IndInv_Unforg_TLC helps TLC reduce the
 *     number of initial states.    
 *)                
IndInv_Unforg_TLC ==  
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality( Corr ) >= N - T
  /\ Faulty = Proc \ Corr
  /\ \A i \in Proc : pc[i] /= "AC"
  /\ sent = {}  
  /\ rcvd \in [ Proc -> sent \cup SUBSET ByzMsgs ]
  
IndInv_Unforg ==  
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}  
  /\ pc = [ i \in Proc |-> "V0" ]        
 
(* If the user wants to check IndInv_Unforg_TLC, he should add a counter to know 
 * how many transition steps are considered. It must be at most 1.
 * Notice that: we don't care about newMessages in IndInv_Unforg(_TLC).
 *) 
Init0 == IndInv_Unforg_TLC /\ newMessages = {}                                          


Next0 ==  
  /\ (\E self \in Corr: Step(self))
(* remember that only moving forward one step
 * when checking an inductive invariant with TLC
 */\ nStep = 1 
 *)
 
Spec0 == Init0 /\ [][Next0]_vars 
               /\ WF_vars(\E self \in Corr: /\ Receive(self)
                                            /\ \/ UponV1(self)
                                               \/ UponNonFaulty(self)
                                               \/ UponAcceptNotSent(self)
                                               \/ UponAccept(self))

(* Some theories about cardinalities used in our proof but cannot proved with TLAPS
 * CardThm, FiniteSetThm1 are copied from Lamport's handout, for more info please
 * visit http://research.microsoft.com/en-us/um/people/lamport/handout.pdf. 
 * CardThm2, SetEnumProp, PWUCard, FiniteSetThm2, UMCardThm, ByzMsgsCard, and ByzMsgsProp 
 * are added by Thanh Hai.  
 *)

THEOREM CardThm == \A S : IsFiniteSet(S) =>
                               /\ Cardinality(S) \in Nat
                               /\ (Cardinality(S) = 0) <=> (S = {})
                               /\ (Cardinality(S) = 1) <=> (\E x \in S : S = { x }) 
  PROOF OMITTED
 
THEOREM CardThm2 == \A X, Y : X \subseteq Y => Cardinality(X) <= Cardinality(Y)   
  PROOF OMITTED 
  
THEOREM SetEnumProp == \A K \in Nat : K > 0 => (Cardinality(1..K) = K /\ IsFiniteSet(1..K))
  PROOF OMITTED  

(* PWU means point-wise update. Notice that in one transition step of 
 * asynchronous algorithms, only one process changes its state or its local variables.
 *)  
THEOREM PWUCard == \A S, x  : IsFiniteSet(S) /\ x \notin S => Cardinality(S \cup {x}) = Cardinality(S) + 1
  PROOF OMITTED            
  
THEOREM EmptySetProp == IsFiniteSet({}) /\ Cardinality({}) = 0
  PROOF OMITTED                        

THEOREM FiniteSetThm1 == \A S, x : IsFiniteSet(S) =>
                                    /\ IsFiniteSet(S \cup { x })
                                    /\ IsFiniteSet(S \ { x })                                    
  PROOF OMITTED    
  
THEOREM FiniteSetThm2 == \A X, Y : (IsFiniteSet(Y) /\ X \subseteq Y) => IsFiniteSet(X)
  PROOF OMITTED      

(* If we have 
 *    1/ X, Y, and Z are finite,
 *    2/ X and Y are disjoint, and
 *    3/ the union of X and Y is Z,
 * then we have the sum of Card(X) and Card(Y) is Card(Z). *)   
THEOREM UMCardThm == 
  \A X, Y, Z :    
    /\ IsFiniteSet(X) 
    /\ IsFiniteSet(Y) 
    /\ IsFiniteSet(Z) 
    /\ X \cup Y = Z
    /\ X = Z \ Y
    => Cardinality(X) = Cardinality(Z) - Cardinality(Y)  
  PROOF OMITTED       
  
(* Two following properties are correct because of the defintion of ByzMsgs *)  
THEOREM ByzMsgsCard == Cardinality(ByzMsgs) = Cardinality(Faulty)
  PROOF OMITTED          
  
THEOREM ByzMsgsProp == IsFiniteSet(Faulty) => IsFiniteSet(ByzMsgs)
  OMITTED  

(* The constraints between N, T, and F *)
THEOREM NTFRel == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0) /\ N - 2*T >= T + 1
  BY NTF
  
(* Proc is always a finite set and its cardinality is N *)  
 THEOREM ProcProp == Cardinality(Proc) = N /\ IsFiniteSet(Proc) /\ Cardinality(Proc) \in Nat
  BY NTF, SetEnumProp, CardThm DEF Proc 
  
   
(* In the following, we try to prove that 
 *    1/ FCConstraints, TypeOK and IndInv_Unforg are inductive invariants, and
 *    2/ IndInv_Unforg implies Unforg.
 *
 * A template proof for an inductive invariant Spec => IndInv is
 *    1. Init => IndInv
 *    2. IndInv /\ [Next]_vars => IndInv'
 *        2.1 IndInv /\ Next => IndInv'
 *        2.2 IndInv /\ UNCHANGED vars => IndInv'
 *    3. Spec => IndInv  
 * Some adivces:
 *    - Rewrite Next (or Step) as much as possible.
 *    - Rewrite IndInv' such that the primed operator appears only after constants or variables.
 *    - Remember to use a constraint Cardinality(X) \in Nat for some finite set X 
 *      when reasoning about the cardinality.        
 *    - Different strings are not equivalent.
 *)

(* FCConstraints is an inductive invariant of SpecNoBcast *) 
(* InitNoBcast => FCConstraints *)    
THEOREM FCConstraints_InitNoBcast == 
  InitNoBcast => FCConstraints
  <1> SUFFICES ASSUME InitNoBcast
           PROVE  FCConstraints
    OBVIOUS       
  <1>1 Corr \subseteq Proc
    BY DEF Init0, Proc, InitNoBcast
  <1>2 Faulty \subseteq Proc
    BY DEF Init0, Proc, InitNoBcast          
  <1>3 IsFiniteSet(Corr)
    BY <1>1, ProcProp, FiniteSetThm2     
  <1>4 IsFiniteSet(Faulty)
    BY <1>2, ProcProp, FiniteSetThm2
  <1>5 Corr \cup Faulty = Proc 
    BY DEF Init0, Proc, InitNoBcast  
  <1>6 Faulty = Proc \ Corr
    BY DEF Init0, Proc, InitNoBcast  
  <1>7 Cardinality(Corr) >= N - T
    <2>1 Cardinality(Corr) \in Nat
      BY <1>3, CardThm
    <2>2 Cardinality(Corr) >= N - F
      BY DEF InitNoBcast         
    <2>3 N - F >= N - T
      BY NTFRel
    <2>4 QED
      BY <2>1, <2>2, <2>3, NTFRel 
  <1>8 Cardinality(Faulty) <= T          
    <2>1 Cardinality(Corr) \in Nat
      BY <1>3, CardThm
    <2>2 Cardinality(Proc) - Cardinality(Corr) <= T
      BY <1>7, <2>1, ProcProp, NTFRel
    <2>3 QED
      BY <1>3, <1>4, <1>5, <1>6, <2>2, UMCardThm, ProcProp 
  <1>9 ByzMsgs \subseteq Proc \X M
    BY  <1>2 DEFS ByzMsgs, M
  <1>10 QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF FCConstraints   

THEOREM FCConstraints_Next ==
  FCConstraints /\ Next => FCConstraints'          
  <1> SUFFICES ASSUME FCConstraints,
                      NEW i \in Corr,
                      Step(i)
                 PROVE FCConstraints'
                 BY DEF Next
  <1>1 Step(i) <=>            
            \/ Receive(i) /\ UponV1(i)
            \/ Receive(i) /\ UponNonFaulty(i) 
            \/ Receive(i) /\ UponAcceptNotSent(i)
            \/ Receive(i) /\ UponAccept(i)            
            \/ Receive(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
    BY DEF Step    
  <1>2 CASE Receive(i) /\ UponV1(i)
    BY <1>2 DEF Receive, UponV1, FCConstraints, ByzMsgs
  <1>3 CASE Receive(i) /\ UponNonFaulty(i)
    BY <1>3 DEF Receive, UponNonFaulty, FCConstraints, ByzMsgs
  <1>4 CASE Receive(i) /\ UponAcceptNotSent(i)
    BY <1>4 DEF Receive, UponAcceptNotSent, FCConstraints, ByzMsgs 
  <1>5 CASE Receive(i) /\ UponAccept(i)
    BY <1>5 DEF Receive, UponAccept, FCConstraints, ByzMsgs  
  <1>6 CASE Receive(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
    BY <1>6 DEF FCConstraints, ByzMsgs   
  <1>7 QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Step      
  
    
(* FCConstraints is an inductive invariant of SpecNoBcast. 
 * We prove this theorem to ensure that what we do with TLC is correct.
 *)      
THEOREM FCConstraints_Init0 == 
  Init0 => FCConstraints
  <1> SUFFICES ASSUME Init0
           PROVE  FCConstraints
    OBVIOUS       
  <1>1 Corr \subseteq Proc
    BY DEF Init0, Proc, IndInv_Unforg_TLC
  <1>2 Faulty \subseteq Proc
    BY DEF Init0, Proc, IndInv_Unforg_TLC          
  <1>3 IsFiniteSet(Corr)
    BY <1>1, ProcProp, FiniteSetThm2     
  <1>4 IsFiniteSet(Faulty)
    BY <1>2, ProcProp, FiniteSetThm2
  <1>5 Corr \cup Faulty = Proc 
    BY DEF Init0, Proc, IndInv_Unforg_TLC  
  <1>6 Faulty = Proc \ Corr
    BY DEF Init0, Proc, IndInv_Unforg_TLC  
  <1>7 Cardinality(Corr) >= N - T
    BY DEF Init0, Proc, IndInv_Unforg_TLC  
  <1>8 Cardinality(Faulty) <= T          
    <2>1 Cardinality(Corr) \in Nat
      BY <1>3, CardThm
    <2>2 Cardinality(Proc) - Cardinality(Corr) <= T
      BY <1>7, <2>1, ProcProp, NTFRel
    <2>3 QED
      BY <1>3, <1>4, <1>5, <1>6, <2>2, UMCardThm, ProcProp 
  <1>9 ByzMsgs \subseteq Proc \X M
    BY  <1>2 DEFS ByzMsgs, M
  <1>10 QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9 DEF FCConstraints      
    
THEOREM FCConstraints_Next0 ==
  FCConstraints /\ Next0 => FCConstraints'
    BY FCConstraints_Next DEF Next0, Next      
      
THEOREM FCConstraints_Proof == Spec0 => FCConstraints
<1>1 Init0 => FCConstraints
  BY FCConstraints_Init0
<1>2 /\ FCConstraints
     /\ [Next]_vars 
  => FCConstraints
  <2>1 CASE Next
    BY FCConstraints_Next0
  <2>2 CASE UNCHANGED vars
    BY <2>2 DEFS vars     
  <2>3 QED 
    BY <2>1, <2>2       
<1> QED
  BY <1>1, <1>2 DEF Spec0           


(* Prove that TypeOK is an inductive invariant of both Spec0 and SpecNoBcast *) 
THEOREM TypeOK_Init0 == Init0 => TypeOK                       
<1> SUFFICES ASSUME Init0
             PROVE TypeOK
      OBVIOUS
  <1>1 sent \subseteq Proc \times M
    BY DEFS Init0, IndInv_Unforg_TLC
  <1>2 pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
    BY DEFS Init0, IndInv_Unforg_TLC  
  <1>3 Corr \subseteq Proc
    BY DEFS Init0, IndInv_Unforg_TLC
  <1>4 Faulty \subseteq Proc
    BY DEF Init0, IndInv_Unforg_TLC
  <1>5 newMessages \in SUBSET ( sent \cup ByzMsgs )
    BY DEFS Init0, IndInv_Unforg_TLC   
  <1>6 rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]   
    <2>1 ByzMsgs \subseteq Proc \times M
      BY <1>4 DEFS ByzMsgs, Proc, M
    <2>2 QED
      BY <1>1, <2>1 DEFS Init0, IndInv_Unforg_TLC, Proc, M    
  <1>8 QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Init0, IndInv_Unforg_TLC, TypeOK
   
THEOREM TypeOK_InitNoBcast == InitNoBcast => TypeOK                       
<1> SUFFICES ASSUME InitNoBcast
             PROVE TypeOK
      OBVIOUS
  <1>1 sent \subseteq Proc \times M
    BY DEFS InitNoBcast
  <1>2 pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
    BY DEFS InitNoBcast  
  <1>3 Corr \subseteq Proc
    BY DEFS InitNoBcast
  <1>4 Faulty \subseteq Proc
    BY DEF InitNoBcast
  <1>5 newMessages \in SUBSET ( sent \cup ByzMsgs )
    BY DEFS InitNoBcast   
  <1>6 rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]   
    <2>1 {} \in SUBSET (Proc \times M)
      BY <1>4 DEFS ByzMsgs, Proc, M
    <2>2 QED
      BY <1>1, <2>1 DEFS InitNoBcast, Proc, M    
  <1>8 QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6 DEF Init0, TypeOK     
    
THEOREM TypeOK_Next == TypeOK /\ Next => TypeOK'
<1> SUFFICES ASSUME TypeOK,
                    NEW i \in Corr,
                    Step(i)
                 PROVE  TypeOK'
          BY DEF Next
  <1>1 Step(i) <=>            
            \/ Receive(i) /\ UponV1(i)
            \/ Receive(i) /\ UponNonFaulty(i) 
            \/ Receive(i) /\ UponAcceptNotSent(i)
            \/ Receive(i) /\ UponAccept(i)            
            \/ Receive(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
      BY DEF Step
  <1>2 TypeOK' =   
          /\ sent' \subseteq Proc' \times M'
          /\ pc' \in [ Proc' -> {"V0", "V1", "SE", "AC"} ]
          /\ Corr' \subseteq Proc'
          /\ Faulty' \subseteq Proc' 
          /\ newMessages' \in SUBSET ( sent' \cup ByzMsgs' )
          /\ rcvd' \in [ Proc' -> SUBSET (sent' \cup ByzMsgs') ]                      
      BY  DEF TypeOK  
  <1>3 CASE Receive(i) /\ UponV1(i)
    <2>1 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
      BY <1>3 DEFS UponV1, TypeOK
    <2>2 Corr' \subseteq Proc'
      BY <1>3 DEFS UponV1, TypeOK
    <2>3 Faulty' \subseteq Proc'
      BY <1>3 DEFS UponV1, TypeOK    
    <2>4 sent' \subseteq Proc' \times M'
      <3>1 i \in Proc
        BY <1>3 DEFS TypeOK
      <3>2 << i, "ECHO">> \in Proc' \times M'
        BY <1>3, <3>1 DEFS Proc, M 
      <3>3 { << i, "ECHO">> } \subseteq Proc' \times M'
        BY <3>2
      <3>4 sent \subseteq Proc' \times M'
        BY <1>3 DEFS TypeOK, M, Proc
      <3>5 QED
        BY <1>3, <3>3, <3>4 DEFS UponV1, TypeOK            
    <2>5 newMessages' \in SUBSET ( sent' \cup ByzMsgs' )
      <3>1 sent \subseteq sent'
        BY <1>3 DEFS UponV1
      <3>2 Faulty' = Faulty
        BY <1>3 DEFS UponV1
      <3>3 ByzMsgs \subseteq ByzMsgs'
        BY <1>3, <3>2 DEF ByzMsgs  
      <3>4 QED
        BY <1>3, <3>1, <3>3 DEFS Receive, TypeOK         
     <2>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]    
      <3>1 Faulty \subseteq Faulty'
        BY <1>3 DEFS UponV1
      <3>2 ByzMsgs \subseteq ByzMsgs'
        BY <3>1 DEF ByzMsgs
      <3>3 sent \subseteq sent'
        BY  <1>3 DEF UponV1
      <3>4 (sent \cup ByzMsgs)  \subseteq (sent' \cup ByzMsgs')
        BY <3>2, <3>3
      <3>5 QED             
        BY <1>3, <2>5, <3>4 DEFS UponV1, TypeOK, Receive
    <2>7 QED
      BY <1>2, <1>3, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
  <1>4 CASE Receive(i) /\ UponNonFaulty(i)
      <2>1 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
      BY <1>4 DEFS UponNonFaulty, TypeOK
    <2>2 Corr' \subseteq Proc'
      BY <1>4 DEFS UponNonFaulty, TypeOK
    <2>3 Faulty' \subseteq Proc'
      BY <1>4 DEFS UponNonFaulty, TypeOK    
    <2>4 sent' \subseteq Proc' \times M'
      <3>1 i \in Proc
        BY <1>4 DEFS TypeOK
      <3>2 << i, "ECHO">> \in Proc' \times M'
        BY <1>4, <3>1 DEFS Proc, M 
      <3>3 { << i, "ECHO">> } \subseteq Proc' \times M'
        BY <3>2
      <3>4 sent \subseteq Proc' \times M'
        BY <1>4 DEFS TypeOK, M, Proc
      <3>5 QED
        BY <1>4, <3>3, <3>4 DEFS UponNonFaulty, TypeOK            
    <2>5 newMessages' \in SUBSET ( sent' \cup ByzMsgs' )
      <3>1 sent \subseteq sent'
        BY <1>4 DEFS UponNonFaulty
      <3>2 Faulty' = Faulty
        BY <1>4 DEFS UponNonFaulty
      <3>3 ByzMsgs \subseteq ByzMsgs'
        BY <1>4, <3>2 DEF ByzMsgs  
      <3>4 QED
        BY <1>4, <3>1, <3>3 DEFS Receive, TypeOK         
     <2>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]    
      <3>1 Faulty \subseteq Faulty'
        BY <1>4 DEFS UponNonFaulty
      <3>2 ByzMsgs \subseteq ByzMsgs'
        BY <3>1 DEF ByzMsgs
      <3>3 sent \subseteq sent'
        BY  <1>4 DEF UponNonFaulty
      <3>4 (sent \cup ByzMsgs)  \subseteq (sent' \cup ByzMsgs')
        BY <3>2, <3>3
      <3>5 QED             
        BY <1>4, <2>5, <3>4 DEFS UponNonFaulty, TypeOK, Receive
    <2>7 QED
      BY <1>2, <1>4, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
  <1>5 CASE Receive(i) /\ UponAcceptNotSent(i)
    <2>1 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
      BY <1>5 DEFS UponAcceptNotSent, TypeOK
    <2>2 Corr' \subseteq Proc'
      BY <1>5 DEFS UponAcceptNotSent, TypeOK
    <2>3 Faulty' \subseteq Proc'
      BY <1>5 DEFS UponAcceptNotSent, TypeOK    
    <2>4 sent' \subseteq Proc' \times M'
      <3>1 i \in Proc
        BY <1>5 DEFS TypeOK
      <3>2 << i, "ECHO">> \in Proc' \times M'
        BY <1>5, <3>1 DEFS Proc, M 
      <3>3 { << i, "ECHO">> } \subseteq Proc' \times M'
        BY <3>2
      <3>4 sent \subseteq Proc' \times M'
        BY <1>5 DEFS TypeOK, M, Proc
      <3>5 QED
        BY <1>5, <3>3, <3>4 DEFS UponAcceptNotSent, TypeOK            
    <2>5 newMessages' \in SUBSET ( sent' \cup ByzMsgs' )
      <3>1 sent \subseteq sent'
        BY <1>5 DEFS UponAcceptNotSent
      <3>2 Faulty' = Faulty
        BY <1>5 DEFS UponAcceptNotSent
      <3>3 ByzMsgs \subseteq ByzMsgs'
        BY <1>5, <3>2 DEF ByzMsgs  
      <3>4 QED
        BY <1>5, <3>1, <3>3 DEFS Receive, TypeOK         
     <2>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]    
      <3>1 Faulty \subseteq Faulty'
        BY <1>5 DEFS UponAcceptNotSent
      <3>2 ByzMsgs \subseteq ByzMsgs'
        BY <3>1 DEF ByzMsgs
      <3>3 sent \subseteq sent'
        BY  <1>5 DEF UponAcceptNotSent
      <3>4 (sent \cup ByzMsgs)  \subseteq (sent' \cup ByzMsgs')
        BY <3>2, <3>3
      <3>5 QED             
        BY <1>5, <2>5, <3>4 DEFS UponAcceptNotSent, TypeOK, Receive
    <2>7 QED
      BY <1>2, <1>5, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK
  <1>6 CASE Receive(i) /\ UponAccept(i)
    <2>1 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
      BY <1>6 DEFS UponAccept, TypeOK
    <2>2 Corr' \subseteq Proc'
      BY <1>6 DEFS UponAccept, TypeOK
    <2>3 Faulty' \subseteq Proc'
      BY <1>6 DEFS UponAccept, TypeOK    
    <2>4 sent' \subseteq Proc' \times M'
      <3>1 i \in Proc
        BY <1>6 DEFS TypeOK
      <3>2 << i, "ECHO">> \in Proc' \times M'
        BY <1>6, <3>1 DEFS Proc, M 
      <3>3 { << i, "ECHO">> } \subseteq Proc' \times M'
        BY <3>2
      <3>4 sent \subseteq Proc' \times M'
        BY <1>6 DEFS TypeOK, M, Proc
      <3>5 QED
        BY <1>6, <3>3, <3>4 DEFS UponAccept, TypeOK            
    <2>5 newMessages' \in SUBSET ( sent' \cup ByzMsgs' )
      <3>1 sent \subseteq sent'
        BY <1>6 DEFS UponAccept
      <3>2 Faulty' = Faulty
        BY <1>6 DEFS UponAccept
      <3>3 ByzMsgs \subseteq ByzMsgs'
        BY <1>6, <3>2 DEF ByzMsgs  
      <3>4 QED
        BY <1>6, <3>1, <3>3 DEFS Receive, TypeOK         
    <2>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]    
      <3>1 Faulty \subseteq Faulty'
        BY <1>6 DEFS UponAccept
      <3>2 ByzMsgs \subseteq ByzMsgs'
        BY <3>1 DEF ByzMsgs
      <3>3 sent \subseteq sent'
        BY  <1>6 DEF UponAccept
      <3>4 (sent \cup ByzMsgs)  \subseteq (sent' \cup ByzMsgs')
        BY <3>2, <3>3
      <3>5 QED             
        BY <1>6, <2>5, <3>4 DEFS UponAccept, TypeOK, Receive
    <2>7 QED
      BY <1>2, <1>6, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK  
  <1>7 CASE Receive(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
    <2>1 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
      BY <1>7 DEF TypeOK
    <2>2 Corr' \subseteq Proc'
      BY <1>7 DEF TypeOK
    <2>3 Faulty' \subseteq Proc'
      BY <1>7 DEF TypeOK
    <2>4 sent' \subseteq Proc' \times M'
      BY <1>7 DEF TypeOK        
    <2>5 newMessages' \in SUBSET ( sent' \cup ByzMsgs' )
      <3>1 sent \subseteq sent'
        BY <1>7 DEF TypeOK
      <3>2 Faulty' = Faulty
        BY <1>7 
      <3>3 ByzMsgs \subseteq ByzMsgs'
        BY <1>7, <3>2 DEF ByzMsgs  
      <3>4 QED
        BY <1>7, <3>1, <3>3 DEFS Receive, TypeOK         
    <2>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]   
      <3>1 Faulty \subseteq Faulty'
        BY <1>7
      <3>2 ByzMsgs \subseteq ByzMsgs'
        BY <3>1 DEF ByzMsgs
      <3>3 sent \subseteq sent'
        BY  <1>7
      <3>4 (sent \cup ByzMsgs)  \subseteq (sent' \cup ByzMsgs')
        BY <3>2, <3>3
      <3>5 QED             
        BY <1>7, <2>5, <3>4 DEFS TypeOK, Receive
    <2>7 QED
      BY <1>2, <1>7, <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF TypeOK  
  <1>8 QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7 DEF Step  
  
THEOREM TypeOKThm == SpecNoBcast => TypeOK
<1>1 InitNoBcast => TypeOK
  BY TypeOK_InitNoBcast
<1>2 /\ TypeOK
     /\ [Next]_vars 
  => TypeOK'
  <2> SUFFICES ASSUME TypeOK,
                      Next \/ UNCHANGED vars 
               PROVE  TypeOK'
        OBVIOUS
  <2>1 CASE Next    
    BY <2>1, TypeOK_Next DEFS Next, Next 
  <2>2 CASE UNCHANGED vars
    <3>1 sent' \subseteq Proc \times M
      BY <2>2 DEFS vars, TypeOK
    <3>2 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
      BY <2>2 DEFS vars, TypeOK  
    <3>3 Corr' \subseteq Proc'
      BY <2>2 DEFS vars, TypeOK
    <3>4 Faulty' \subseteq Proc'
      BY <2>2 DEF vars, TypeOK
    <3>5 newMessages' \in SUBSET ( sent' \cup ByzMsgs' )
      <4>1 newMessages' = newMessages
        BY <2>2 DEF vars
      <4>2 sent' = sent
        BY <2>2 DEF vars
      <4>3 ByzMsgs' = ByzMsgs
        BY <2>2 DEF vars, ByzMsgs
      <4>4 QED
        BY <2>2, <4>1, <4>2, <4>3 DEFS vars, TypeOK   
    <3>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]   
      <4>1 rcvd' = rcvd
        BY <2>2 DEF vars
      <4>2 sent' = sent
        BY <2>2 DEF vars
      <4>3 ByzMsgs' = ByzMsgs
        BY <2>2 DEF vars, ByzMsgs
      <4>4 QED
        BY <2>2, <3>1, <4>1, <4>2, <4>3 DEFS TypeOK    
    <3>7 TypeOK' =    
          /\ sent' \subseteq Proc \times M
          /\ pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
          /\ Corr' \subseteq Proc'
          /\ Faulty' \subseteq Proc'
          /\ newMessages' \in SUBSET ( sent' \cup ByzMsgs' )
          /\ rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]  
      BY DEF TypeOK        
    <3>8 QED
      BY <2>2, <3>1, <3>2, <3>3, <3>4, <3>5, <3>6, <3>7 DEFS  TypeOK, vars
  <2>3 QED 
    BY <2>1, <2>2       
<1> QED
  BY <1>1, <1>2 DEF SpecNoBcast, TypeOK         
  
THEOREM Step0 == pc = [i \in Proc |-> "V0" ] => \A i \in Proc : pc[i] # "AC"
  OBVIOUS  

(* The following is the main part of our proof. We prove that IndInv_Unforg is an
 * inductive invariant.  
 *)  
THEOREM Unforg_Step1 == InitNoBcast => IndInv_Unforg     
  <1>1 InitNoBcast => TypeOK
    BY TypeOK_InitNoBcast
  <1>2 InitNoBcast => FCConstraints
    BY FCConstraints_InitNoBcast    
  <1>3 InitNoBcast => sent = {}
    BY DEF InitNoBcast  
  <1>4 InitNoBcast => pc = [ i \in Proc |-> "V0" ]
    BY DEF InitNoBcast  
  <1>5 QED
    BY <1>1, <1>2, <1>3, <1>4 DEF IndInv_Unforg
    
THEOREM Unforg_Step2 == IndInv_Unforg /\ Next => IndInv_Unforg'     
  <1>1 IndInv_Unforg /\ Next => TypeOK'
    BY TypeOK_Next DEF IndInv_Unforg
  <1>2 IndInv_Unforg /\ Next => FCConstraints'
    BY FCConstraints_Next DEF IndInv_Unforg    
  <1>3 TypeOK' =   
          /\ sent' \subseteq Proc' \times M'
          /\ pc' \in [ Proc' -> {"V0", "V1", "SE", "AC"} ]
          /\ Corr' \subseteq Proc'
          /\ Faulty' \subseteq Proc' 
          /\ newMessages' \in SUBSET ( sent' \cup ByzMsgs' )
          /\ rcvd' \in [ Proc' -> SUBSET (sent' \cup ByzMsgs') ]                      
      BY  DEF TypeOK  
  <1>4 IndInv_Unforg /\ Next => (sent' = {} /\ pc' = [ j \in Proc |-> "V0" ])
    <2> SUFFICES ASSUME TypeOK,
                        FCConstraints,
                        sent = {},
                        pc = [ i \in Proc |->  "V0" ],
                        NEW i \in Corr,
                        Step(i)
                 PROVE  sent' = {} /\ pc' = [ j \in Proc |-> "V0" ]
          BY DEF Next, IndInv_Unforg
    <2>1 Step(i) <=>
            \/ Receive(i) /\ UponV1(i)
            \/ Receive(i) /\ UponNonFaulty(i) 
            \/ Receive(i) /\ UponAcceptNotSent(i)
            \/ Receive(i) /\ UponAccept(i)            
            \/ Receive(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
      BY DEF Step
    <2>2 CASE Receive(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>  
      BY <2>2 DEF IndInv_Unforg   
    <2>3 IndInv_Unforg /\ Receive(i) => Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
      <3> SUFFICES ASSUME TypeOK,
                          FCConstraints,
                          sent = {},
                          pc = [ j \in Proc |->  "V0" ],
                          Receive(i)
                   PROVE  Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
            BY DEF IndInv_Unforg
      <3>1 sent = {}
        OBVIOUS
      <3>2 sent \cup ByzMsgs = ByzMsgs
        OBVIOUS
      <3>3 newMessages' \in SUBSET (sent \cup ByzMsgs)
        BY DEF Receive
      <3>4 newMessages' \in SUBSET ByzMsgs
        BY <3>1, <3>3
      <3>5 newMessages' \subseteq ByzMsgs
        BY <3>4
      <3>6 rcvd[i] \subseteq sent \cup ByzMsgs
        BY DEF TypeOK
      <3>7 rcvd[i] \subseteq ByzMsgs
        BY <3>6, <3>2      
      <3>8 rcvd'[i] \subseteq ByzMsgs
        <4>1 Corr \subseteq Proc
          BY DEF TypeOK
        <4>2 i \in Proc
          BY <4>1
        <4>3 QED
          BY <3>4, <3>7, <4>2 DEF Receive
      <3>9 Cardinality(Faulty) <= T
        BY DEF FCConstraints
      <3>10 Cardinality(ByzMsgs) = Cardinality(Faulty)
        BY ByzMsgsCard
      <3>11 Cardinality(ByzMsgs) <= T
        BY <3>9, <3>10        
      <3>12 Cardinality(rcvd'[i]) <= Cardinality(ByzMsgs)
        BY <3>8, CardThm2
      <3>13 Cardinality(ByzMsgs) \in Nat
        BY ByzMsgsProp, CardThm DEF FCConstraints
      <3>14 IsFiniteSet(Faulty)
        BY DEF FCConstraints
      <3>15 IsFiniteSet(ByzMsgs)
        BY <3>14, ByzMsgsProp
      <3>16 IsFiniteSet(rcvd'[i])
        BY <3>15, <3>8, FiniteSetThm2
      <3>17 Cardinality(rcvd'[i]) \in Nat
        BY <3>16, CardThm
      <3>18 QED
        BY <3>17, <3>13, <3>11, <3>12, NTF
    <2>4 IndInv_Unforg /\ Receive(i) => ~UponV1(i)
      <3>1 Corr \subseteq Proc
        BY DEF TypeOK
      <3>2 pc[i] = "V0"
        BY <3>1
      <3>3 pc[i] # "V1"
        BY <3>2 
      <3>10 QED 
        BY <3>3 DEF UponV1, IndInv_Unforg                              
    <2>5 IndInv_Unforg /\ Receive(i) => ~UponNonFaulty(i) 
      <3> SUFFICES ASSUME IndInv_Unforg,
                          Receive(i)
                   PROVE ~UponNonFaulty(i)                   
            OBVIOUS
      <3>1 ~UponNonFaulty(i) =
              \/ ~(pc[i] /= "SE")
              \/ ~(Cardinality(rcvd'[i]) >= T + 1)
              \/ ~(Cardinality(rcvd'[i]) < N - T)
              \/ ~(pc' = [pc EXCEPT ![i] = "SE"])
              \/ ~(sent' = sent \cup { <<i, "ECHO">> })
              \/ ~(UNCHANGED << Corr, Faulty >>)
        BY DEF UponNonFaulty      
      <3>2 ~(Cardinality(rcvd'[i]) >= T + 1)
                = (Cardinality(rcvd'[i]) <= T)  
        BY <2>3, NTF
      <3>3 Cardinality(rcvd'[i]) <= T
        BY <2>3  
      <3>4 (Cardinality(rcvd'[i]) <= T) => ~UponNonFaulty(i)
        BY <2>4, NTF, <3>1, <3>2, <3>3            
      <3>5 QED
        BY <3>3, <3>4
    <2>6 IndInv_Unforg /\ Receive(i) => ~UponAcceptNotSent(i) 
      <3> SUFFICES ASSUME IndInv_Unforg,
                          Receive(i)
                   PROVE ~UponAcceptNotSent(i)                   
            OBVIOUS
      <3>1 ~UponAcceptNotSent(i) =
              \/ ~(pc[i] \in { "V0", "V1" } )
              \/ ~(Cardinality(rcvd'[i]) >= N - T)              
              \/ ~(pc' = [pc EXCEPT ![i] = "AC"])
              \/ ~(sent' = sent \cup { <<i, "ECHO">> })
              \/ ~(UNCHANGED << Corr, Faulty >>)
        BY DEF UponAcceptNotSent  
      <3>2 (Cardinality(rcvd'[i]) <= T)
              => (Cardinality(rcvd'[i]) < N - T)
        BY <2>3, NTFRel 
      <3>3 ~(Cardinality(rcvd'[i]) >= N - T) 
              = (Cardinality(rcvd'[i]) < N - T)
        BY <2>3, NTFRel    
      <3>4 (Cardinality(rcvd'[i]) <= T) 
              => ~(Cardinality(rcvd'[i]) >= N - T)
        BY <3>2, <3>3   
      <3>5 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptNotSent(i)
        BY <3>1, <3>4              
      <3>6 QED
        BY <2>3, <3>5        
    <2> IndInv_Unforg /\ Receive(i) =>  ~UponAccept(i)
      <3> SUFFICES ASSUME IndInv_Unforg,
                          Receive(i)
                   PROVE ~UponAccept(i)                   
            OBVIOUS
      <3>1 ~UponAccept(i) =
              \/ ~(pc[i] = "SE")
              \/ ~(Cardinality(rcvd'[i]) >= N - T)              
              \/ ~(pc' = [pc EXCEPT ![i] = "AC"])
              \/ ~(sent' = sent)
              \/ ~(UNCHANGED << Corr, Faulty >>)
        BY DEF UponAccept  
      <3>2 (Cardinality(rcvd'[i]) <= T)
              => (Cardinality(rcvd'[i]) < N - T)
        BY <2>3, NTFRel 
      <3>3 ~(Cardinality(rcvd'[i]) >= N - T) 
              = (Cardinality(rcvd'[i]) < N - T)
        BY <2>3, NTFRel    
      <3>4 (Cardinality(rcvd'[i]) <= T) 
              => ~(Cardinality(rcvd'[i]) >= N - T)
        BY <3>2, <3>3   
      <3>5 (Cardinality(rcvd'[i]) <= T) => ~UponAccept(i)
        BY <3>1, <3>4              
      <3>6 QED
        BY <2>3, <3>5        
    <2>10 QED
        BY <2>1, <2>2, <2>3, <2>4, <2>5, <2>6 DEF Step, IndInv_Unforg
  <1>5 QED
    BY <1>1, <1>2, <1>3, <1>4 DEF IndInv_Unforg    
  
THEOREM Unforg_Step3 == IndInv_Unforg => Unforg
  <1>1 pc = [i \in Proc |-> "V0" ] => \A i \in Proc : pc[i] # "AC"
    OBVIOUS
  <1>2 (TypeOK /\ pc = [i \in Proc |-> "V0" ]) => \A i \in Proc : pc[i] # "AC"
    BY <1>1
  <1>3 (TypeOK /\ FCConstraints /\ pc = [i \in Proc |-> "V0" ]) => \A i \in Proc : pc[i] # "AC"
    BY <1>2
  <1>4 (TypeOK /\ FCConstraints /\ pc = [i \in Proc |-> "V0" ] /\ sent = {}) => \A i \in Proc : pc[i] # "AC"    
    BY <1>3
  <1>5 IndInv_Unforg => \A i \in Proc : pc[i] # "AC"   
    BY <1>4 DEF IndInv_Unforg  
  <1>6 IndInv_Unforg => \A i \in Proc : i \in Corr => pc[i] # "AC"
    BY  <1>5     
  <1>7 QED
    BY <1>6 DEF Unforg 
    
THEOREM Unforg_Thm == SpecNoBcast => Unforg
  BY Unforg_Step1, Unforg_Step2, Unforg_Step3 DEF SpecNoBcast     

=============================================================================
\* Modification History
\* Last modified Fri Feb 03 15:00:10 CET 2017 by tran
\* Last modified Mon Jan 30 13:45:19 CET 2017 by tran
\* Last modified Thu Jan 26 17:19:44 CET 2017 by TTHAI
\* Last modified Thu Jan 26 15:27:20 CET 2017 by TTHAI
\* Last modified Mon Jan 09 09:40:14 CET 2017 by tran
\* Last modified Sun Jan 01 13:32:35 CET 2017 by TTHAI





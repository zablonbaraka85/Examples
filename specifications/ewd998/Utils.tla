------------------------------- MODULE Utils -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

\* This is mostly copy&pasted from various TLA+ community modules at:
\* https://github.com/tlaplus/CommunityModules/modules

Reduce(op(_,_), fun, from, to, base) == 
  (**************************************************************************)
  (* Reduce the elements in the range from..to of the function's co-domain. *)
  (**************************************************************************)
  LET reduced[i \in from..to] ==
          IF i = from THEN op(base, fun[i])
          ELSE op(reduced[i - 1], fun[i])
  IN reduced[to]

sum(a, b) ==
  a + b

Contains(s, e) ==
  (**************************************************************************)
  (* TRUE iff the element e \in ToSet(s).                                   *)
  (**************************************************************************)
  \E i \in 1..Len(s) : s[i] = e
  
RemoveAt(s, i) == 
  (**************************************************************************)
  (* Replaces the element at position i shortening the length of s by one.  *)
  (**************************************************************************)
  SubSeq(s, 1, i-1) \o SubSeq(s, i+1, Len(s))

Range(f) ==
  { f[x] : x \in DOMAIN f }

(***************************************************************************)
(* The inverse of a function.                                              *)
(***************************************************************************)
Inverse(f,S,T) == [t \in T |-> CHOOSE s \in S : t \in Range(f) => f[s] = t]

\* No support for RECURSIVE in PlusPy.
IsSimpleCycle(S, r) ==
  (* View r as a graph s.t. S is the graph's set of vertices and there 
     exists an edge from s to t iff f[s] = t. IsFiniteSet(DOMAIN r). *)
  LET 
   F[ i \in 1..Cardinality(S) ] == 
         IF i = 1 THEN << CHOOSE s \in S : TRUE >>
         ELSE LET seq == F[i-1]
                  head == Head(seq)
              IN << r[head] >> \o F[i-1]
  IN Range(F[Cardinality(S)]) = S

\* SimpleCycle is a recursive variant of the predicate IsSimpleCycle above. It
\* does not work with PlusPy, but is orders of magnitude faster when evaluated
\* by TLC.
SimpleCycle(S) ==
    LET sts == LET SE == INSTANCE SequencesExt IN SE!SetToSeq(S)
        RECURSIVE SimpleCycle(_,_,_)
        SimpleCycle(seq, prefix, i) ==
            IF i = Len(seq)
            THEN prefix @@ (seq[i] :> seq[1])
            ELSE SimpleCycle(seq, prefix @@ (seq[i] :> seq[i+1]), i+1)
    IN SimpleCycle(sts, sts[1] :> sts[2], 2)

=============================================================================

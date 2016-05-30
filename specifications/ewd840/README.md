# Termination detection in a ring
A specification of Dijkstra's algorithm for termination detection
in a ring. The algorithm was published as 
Edsger W. Dijkstra: Derivation of a termination detection algorithm for distributed computations. Inf. Proc. Letters 16:217-219 (1983).
It appears as [EWD 840](https://www.cs.utexas.edu/users/EWD/ewd08xx/EWD840.PDF).

TLC can be used to verify safety and liveness properties. The TLA+ module also
contains a hierarchical proof of the safety property that is checked by TLAPS.
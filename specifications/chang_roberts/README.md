# Chang-Roberts algorithm for leader election in a ring
An early algorithm for electing a leader in a unidirectional ring
appeared as

E. Chang, R. Roberts: An improved algorithm for decentralized extrema-finding
in circular configurations of processes. CACM 22(5): 281-283, 1979.

The module contains a PlusCal version of that algorithm. For verifying it,
create an instance, e.g.

N <- 6
Id(n) <- IF n=1 THEN 12
         ELSE IF n=2 THEN 27
         ELSE IF n=3 THEN 63
         ELSE IF n=4 THEN 3
         ELSE IF n=5 THEN 45
         ELSE IF n=6 THEN 9
         ELSE "error"

and check the invariants TypeOK and Correctness and the temporal logic
property Liveness.
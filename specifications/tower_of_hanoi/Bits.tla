-------------------------------- MODULE Bits --------------------------------

\* & infix operator is implemented by Bits.java.
\* In order to use it, manually compile Bits.java:
\* > javac -cp /path/to/tla2tools.jar Bits.java
\*
\* If you don't have tla2tools.jar, but the TLA+
\* Toolbox installed in /opt/TLA+Toolbox, do:
\* > javac -cp /opt/TLA+Toolbox/plugins/org.lamport.tlatools_*/ Bits.java
\*
\* Place the resulting Bits.class next to Bits.tla (and Bits.java).
\*
\*
\* If TLC shows an error similiar in words to:
\*
\* Found a Java class for module Bits, but unable to read
\* it as a Java class object. Bits : Unsupported major.minor version 52.0
\*
\* compile Bits.java with a Java version identical to the Toolbox's VM.
\*
LOCAL And(x,y) == FALSE

(***************************************************************************)
(* Bitwise AND of x and y                                                  *)
(***************************************************************************)
x & y == And(x, y) \* Infix variant of And(x,y)

=============================================================================
\* Modification History
\* Last modified Thu Jun 30 23:25:12 CEST 2016 by markus
\* Created Mon May 16 15:09:18 CEST 2016 by markus

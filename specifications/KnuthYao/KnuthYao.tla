----------------------------------------- MODULE KnuthYao -----------------------------------------
EXTENDS DyadicRationals, CSV, TLC, TLCExt, IOUtils, Naturals

VARIABLES p,     \* The probability we are here   
          state, \* The current state
          flip   \* The current flip

vars == <<p, state, flip>>

Done == {"1", "2", "3", "4", "5", "6"}
Flip == { "H", "T" }

Transition == [s0 |-> [H |-> "s1", T |-> "s2"],
               s1 |-> [H |-> "s3", T |-> "s4"],
               s2 |-> [H |-> "s5", T |-> "s6"],
               s3 |-> [H |-> "s1", T |-> "1" ],
               s4 |-> [H |-> "2",  T |-> "3" ],
               s5 |-> [H |-> "4",  T |-> "5" ],
               s6 |-> [H |-> "6",  T |-> "s2"]]

Heads ==
    /\ flip' = "H"

Tails ==
    \* Crooked coin: Decreasing chance of a tail over time.
    /\ RandomElement(1..p.den) = 1
    /\ flip' = "T"

TossFairCoin == /\ Heads \/ Tails
                /\ p'    = Half(p)
                
Init == /\ state = "s0"
        /\ p     = One
        /\ flip  \in Flip

Next == /\ state  \notin Done
        /\ state' = Transition[state][flip]
        /\ TossFairCoin
        
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* TODO Uncomment once we have a definition of DyadicRationals!DyadicRationals as tracked in https://github.com/tlaplus/CommunityModules/issues/63
\* THEOREM Converges == \A e \in DyadicRationals \ {0} : Spec => <>(state \in Done \/ p < e) 

----------------------------------------------------------------------------------------------------

\* The data collection below only works with TLC running in generation mode.
\* Unless TLC runs with -Dtlc2.tool.impl.Tool.probabilistic=true (or -generate),
\* the simulator generates all successor states from which it chooses one randomly. 
\* In "generate" mode, however, TLC randomly generates a (single) successor state.
ASSUME TLCGet("config").mode = "generate"
\* Do not artificially restrict the length of behaviors.
ASSUME TLCGet("config").depth >= 10
\* The algorithm terminates. Thus, do not check for deadlocks.
ASSUME TLCGet("config").deadlock = FALSE
\* Require a recent versions of TLC with support for the operators appearing below.
ASSUME TLCGet("revision").timestamp >= 1628119427 

CSVFile ==
    "KnuthYao.csv"

ASSUME 
    CSVRecords(CSVFile) = 0 => CSVWrite("side,p,flip", <<>>, CSVFile)

Stats ==
    \* Cfg: CONSTRAINT Stats
    /\ state \in Done => 
        /\ CSVWrite("%1$s,%2$s,%3$s", <<state, p.den, flip>>, CSVFile)
        \* Update KnuthYao.svg every 100 samples.
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "KnuthYao.R", "KnuthYao.csv">>).exitValue = 0

====================================================================================================

$ rm *.csv ; tlc KnuthYao -generate -note -depth 10
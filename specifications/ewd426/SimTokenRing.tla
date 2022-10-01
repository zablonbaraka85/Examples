-------------------------------- MODULE SimTokenRing -------------------------------
EXTENDS TokenRing, TLC, CSV, IOUtils

(* Statistics collection *)

CSVFile ==
    "SimTokenRing.csv"

ASSUME
    \* Initialize the CSV file with a header.
    /\ CSVRecords(CSVFile) = 0 => CSVWrite("steps", <<>>, CSVFile)

AtStabilization == 
    \* State constraint at cfg
    UniqueToken => 
        /\ CSVWrite("%1$s", <<TLCGet("level")>>,CSVFile)
        /\ TLCGet("stats").traces % 250 = 0 =>
            /\ IOExec(<<"/usr/bin/env", "Rscript", "SimTokenRing.R", CSVFile>>).exitValue = 0        
        /\ FALSE \* to make TLC simulate the next behavior one the system stabilizes.

=======================================================================================
$ rm -rf states/ ; rm *.csv ; tlc SimTokenRing -note -generate -depth -1



$ alias tlc
tlc='java -cp /path/to/tla2tools.jar tlc2.TLC'
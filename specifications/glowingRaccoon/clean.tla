----------------------------- MODULE clean -----------------------------
(* what polymerase chain reaction is, and not how it works *)

EXTENDS Naturals \* an import - copies module in there

CONSTANTS DNA, PRIMER \* starting stock of key things

VARIABLES tee, \* temperature, a string
          primer, \* count of primers remaining
          dna, \* count of double strands present
          template, \* count of single strands present
          hybrid \* count of template-primer hybrids

(* list of state variables, for convenience *)
vars == << tee, primer, dna, template, hybrid >>
          
(* helper function *)
natMin(i,j) == IF i < j THEN i ELSE j \* min of two nats

(* actions *)
heat == /\ tee = "Hot" \* current temperature is "Hot"
        /\ tee' = "TooHot" \* heat up to "TooHot"
        /\ primer' = primer + hybrid \* we'll take those back, thanks
        /\ dna' = 0 \* the dna denatures
        /\ template' = template + hybrid + 2 * dna \* has to go somewhere
        /\ hybrid' = 0 \* these denature too

cool == /\ tee = "TooHot" \* when you just denatured
        /\ tee' = "Hot" \* cool off to "Hot"
        /\ UNCHANGED << primer, dna, template, hybrid >>

anneal == /\ tee = "Hot" \* too hot to anneal primers
          /\ tee' = "Warm" \* "Warm" is just right
          /\ UNCHANGED dna \* dna can reanneal; we neglect that
          (* this is the neat part *)
          /\ \E k \in 1..natMin(primer, template) : \* tweak this - tweaked
             /\ primer' = primer - k \* k consumed
             /\ template' = template - k \* k consumed
             /\ hybrid' = hybrid + k \* k more hybrids

extend == /\ tee = "Warm" \* too cool for extension
            /\ tee' = "Hot" \* "Hot" is just right
            /\ UNCHANGED <<primer, template>>
            /\ dna' = dna + hybrid \* assuming it just happens
            /\ hybrid' = 0 \* all turned to dna
            
(* initial state *)
Init == /\ tee = "Hot" \* not really all that hot
        /\ primer = PRIMER \* we have consumed no primers
        /\ dna = DNA \* we start with some nice 'frozen' dna
        /\ template = 0 \* everything is bound up
        /\ hybrid = 0 \* no annealing has happened yet
            
(* state transition *)
Next ==  \/ heat
         \/ cool
         \/ anneal
         \/ extend

(* specification of system *)
Spec == /\ Init 
        /\ [][Next]_vars 

(* safety *)
primerPositive == (primer >= 0) \* an invariant

constantCount == UNCHANGED ( template + primer + 2*(dna + hybrid) )
strandInvariant == [][constantCount]_vars \* a property

(* liveness *)
primerDepleted == <>(primer = 0) \* does not hold!

=============================================================================

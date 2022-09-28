 ----------------------------- MODULE stages -----------------------------
(* we need higher resolution - adding stages & cycles *)

EXTENDS Naturals \* an import

CONSTANTS DNA, PRIMER \* starting stock of key things

VARIABLES tee, \* temperature
          primer, \* count of primers remaining
          dna, \* count of double strands present
          template, \* count of single strands present
          hybrid, \* count of template-primer hybrids
          stage, \* new arrival - a history of sorts
          cycle \* now we can count...!

(* list of state variables, for convenience *)
vars == << tee, primer, dna, template, hybrid, stage, cycle >>
          
(* helper function *)
natMin(i,j) == IF i < j THEN i ELSE j \* min of two nats

(* steps *)
heat ==    /\ tee = "Hot" \* current temperature is "Hot"
           /\ tee' = "TooHot" \* heat up to "TooHot"
           /\ primer' = primer + hybrid \* we'll take those back, thanks
           /\ dna' = 0 \* the dna denatures
           /\ template' = template + hybrid + 2 * dna \* has to go somewhere
           /\ hybrid' = 0 \* these denature too
           /\ (stage = "init" \/ stage = "extended")
           /\ stage' = "denatured"
           /\ UNCHANGED cycle

cool ==   /\ tee = "TooHot" \* when you just denatured
          /\ tee' = "Hot" \* cool off to "Hot"
          /\ UNCHANGED << cycle, primer, dna, template, hybrid >>
          /\ stage = "denatured"
          /\ stage' = "ready"

anneal ==   /\ tee = "Hot" \* too hot to anneal primers
            /\ tee' = "Warm" \* "Warm" is just right
            /\ UNCHANGED <<cycle, dna>> \* dna can reanneal; we neglect that
            (* this is the neat part *)
            /\ \E k \in 1..natMin(primer, template) : 
                /\ primer' = primer - k \* k consumed
                /\ template' = template - k \* k consumed
                /\ hybrid' = hybrid + k \* k more hybrids
            /\ stage = "ready"
            /\ stage' = "annealed"
            
extend ==   /\ tee = "Warm" \* too cool for extension
            /\ tee' = "Hot" \* "Hot" is just right
            /\ UNCHANGED <<primer, template>>
            /\ dna' = dna + hybrid \* assuming it just happens
            /\ hybrid' = 0 \* all turned to dna
            /\ stage = "annealed"
            /\ stage' = "extended"
            /\ cycle' = cycle + 1 \* only place this changes
            
(* initial state *)
Init == /\ tee = "Hot" \* not really all that hot
        /\ primer = PRIMER \* we have consumed no primers
        /\ dna = DNA \* we start with some nice 'frozen' dna
        /\ template = 0 \* everything is bound up
        /\ hybrid = 0 \* no annealing has happened yet
        /\ stage = "init"
        /\ cycle = 0 \* no cycles completed
            
(* gathering up actions *)
Next == \/ heat
        \/ cool
        \/ anneal
        \/ extend

(* system spec *)
Spec == /\ Init 
        /\ [][Next]_vars 
        /\ SF_vars(anneal) 
        /\ SF_vars(heat)
        /\ SF_vars(cool)
        /\ SF_vars(extend)

cleanInstance == INSTANCE clean
cleanSpec == cleanInstance!Spec
primerDepleted == cleanInstance!primerDepleted



=============================================================================

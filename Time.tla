-------------------------------- MODULE Time --------------------------------

EXTENDS Integers, TLC, Sequences

CONSTANT MAX_T
VARIABLES t, ticked

ASSUME /\ MAX_T > 0

vars == <<t, ticked>>

TypeOK == /\ t \in Nat
          /\ t >= 0
          /\ ticked \in 0..1
          
Init == /\ t = 0
        /\ ticked = 0
        
Finished == t = MAX_T

ConsumeInterval == /\ Finished = FALSE
                   /\ ticked = 0
                   /\ ticked' = 1
                   /\ UNCHANGED <<t>>
                   
DoTick == /\ Finished = FALSE
          /\ ticked = 1
          /\ ticked' = 0
          /\ t' = t + 1
          
Next == \/ ConsumeInterval
        \/ DoTick

Fairness == WF_vars(DoTick) /\ WF_vars(ConsumeInterval)
        
Spec == /\ Init 
        /\ [][Next]_vars 
        /\ Fairness
        
Termination == <>(Finished = TRUE)

=============================================================================
\* Modification History
\* Last modified Thu Oct 27 02:45:12 IRST 2022 by Arvin
\* Created Tue Oct 25 23:09:31 IRST 2022 by Arvin

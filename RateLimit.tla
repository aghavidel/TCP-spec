----------------------------- MODULE RateLimit -----------------------------
EXTENDS Integers, TLC, Sequences

CONSTANT C, MAX_T
VARIABLES t, ticked, service

timeVars == <<t, ticked>>
rateVars == <<service>>
vars == <<t, ticked, service>>

time == INSTANCE Time WITH t <- t, MAX_T <- MAX_T, ticked <- ticked

TypeOK == /\ service \in Nat
          /\ service >= 0
          /\ time!TypeOK

Init == /\ service = 0
        /\ time!Init
        
ServiceEnabled == /\ service < t * C
                  /\ time!Finished = FALSE
                  /\ ticked = 0

Serve == /\ ServiceEnabled
         /\ service' = service + 1
         /\ UNCHANGED timeVars
         
Next == \/ Serve
        \/ /\ time!Next
           /\ UNCHANGED rateVars
        
Spec == Init /\ [][Next]_vars

RateLimited == [] (service <= C * t)

=============================================================================
\* Modification History
\* Last modified Thu Oct 27 00:03:38 IRST 2022 by Arvin
\* Created Tue Oct 25 23:28:20 IRST 2022 by Arvin

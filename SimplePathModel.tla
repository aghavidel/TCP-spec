-------------------------- MODULE SimplePathModel --------------------------
EXTENDS Integers, TLC, Sequences

CONSTANT C, MAX_T, MAX_ARRIVAL
VARIABLES t, ticked, nAck, inFlight, timeout

timeVars == <<t, ticked>>
pathVars == <<nAck, inFlight, timeout>>
vars == <<t, ticked, nAck, inFlight, timeout>>

time == INSTANCE Time WITH t <- t, ticked <- ticked, MAX_T <- MAX_T

TypeOK == /\ timeout \in 0..1
          /\ nAck \in Nat
          /\ nAck >= 0
          /\ inFlight \in Nat
          /\ inFlight >= 0
          /\ time!TypeOK

Init == /\ timeout = 0
        /\ nAck = 0
        /\ inFlight = 0
        /\ time!Init
        
PathModelIsEnabled == /\ inFlight > 0
                      /\ inFlight < t*C
                      /\ ticked = 0
                      /\ time!Finished = FALSE
                      
PacketInjectionIsEnabled == /\ ticked = 1
                            /\ time!Finished = FALSE

DeliverPacket == /\ PathModelIsEnabled
                 /\ timeout' = 0
                 /\ nAck' = nAck + 1
                 /\ inFlight' = inFlight
                 /\ UNCHANGED timeVars
                 
DeliverLate == /\ PathModelIsEnabled 
               /\ timeout' = 1
               /\ nAck' = nAck + 1
               /\ inFlight' = inFlight - 1
               /\ UNCHANGED timeVars
              
DeliverAndDropAck == /\ PathModelIsEnabled
                     /\ timeout' = 1
                     /\ nAck' = nAck
                     /\ inFlight' = inFlight - 1
                     /\ UNCHANGED timeVars
                     
DropCompletely == /\ PathModelIsEnabled
                  /\ timeout' = 1
                  /\ nAck' = nAck
                  /\ inFlight' = inFlight - 1
                  /\ UNCHANGED timeVars
                  
Next == \/ DeliverPacket
        \/ DeliverLate
        \/ DeliverAndDropAck
        \/ DropCompletely
        \/ /\ time!Next
           /\ UNCHANGED pathVars

Spec == Init /\ [][Next]_vars /\ time!Fairness

RateLimited == [] (inFlight <= t * C)

Max(a, b) == IF a > b THEN a ELSE b

Min(a, b) == IF a < b THEN a ELSE b

newPacketsAllowed(timePassed, existingPackets) == Max(timePassed*C - existingPackets - 1, 0)

getRandomArrival(timePassed, existingPackets) == 
    RandomElement(0..Min(MAX_ARRIVAL, newPacketsAllowed(timePassed, existingPackets)))

InjectPackets == /\ PacketInjectionIsEnabled
                 /\ inFlight' = inFlight + getRandomArrival(t, inFlight)
                 /\ nAck' = nAck
                 /\ timeout' = timeout
                 /\ time!DoTick

NextTest == \/ DeliverPacket
            \/ DeliverLate
            \/ DeliverAndDropAck
            \/ DropCompletely
            \/ InjectPackets
            \/ /\ time!Next
               /\ UNCHANGED pathVars
            
Fairness == /\ time!Fairness
            /\ SF_vars(InjectPackets)

SpecTest == Init /\ [][NextTest]_vars /\ Fairness  

Termination == <>(t = MAX_T)

=============================================================================
\* Modification History
\* Last modified Sun Oct 30 23:07:15 IRST 2022 by Arvin
\* Created Thu Oct 27 00:16:46 IRST 2022 by Arvin

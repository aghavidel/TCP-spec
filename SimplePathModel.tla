-------------------------- MODULE SimplePathModel --------------------------
(***************************************************************************)
(* Implements a rate-limited, simple path model for packets traversing it  *)
(* to reach some destination.  The model is able to unconditionally delay, *)
(* drop, or deliver the packets to the destination as will.                *)
(*                                                                         *)
(* ACKs are returned for each delivered packet (though the ACK itself can  *)
(* be dropped as well, but that behavior can be changed).                  *)
(*                                                                         *)
(* The model will trigger timeouts for dropped packets.                    *)
(***************************************************************************)

EXTENDS Integers, TLC, Sequences

(***************************************************************************)
(* C          : The link capacity. After 't' timesteps, no more than 'C*t' *)
(*              packets can be in the link. Any more is immediately        *)
(*              dropped.                                                   *)
(* MAX_ARRIVAL: The maximum rate of packet arrivals.                       *)
(* DROP_ACK   : A boolean constant, if TRUE, the model can drop ACKs on    *)
(*              a whim.                                                    *)
(* nAck       : The number of ACKs returned.                               *)
(* inFlight   : The number of packets traversing the link.                 *)
(* timeout    : If '1', a packet has not reached it's destination and has  *)
(*              timed out.                                                 *)
(***************************************************************************)

CONSTANT C, MAX_T, MAX_ARRIVAL, DROP_ACK
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
        
Finished == time!Finished
        
PathModelIsEnabled == /\ inFlight > 0
                      /\ ticked = 0
                      /\ Finished = FALSE
                      
PacketInjectionIsEnabled == /\ ticked = 1
                            /\ Finished = FALSE

DeliverPacket == /\ PathModelIsEnabled
                 /\ timeout' = 0
                 /\ nAck' = nAck + 1
                 /\ inFlight' = inFlight - 1
                 /\ UNCHANGED timeVars
                 
DeliverLate == /\ PathModelIsEnabled 
               /\ timeout' = 1
               /\ nAck' = nAck + 1
               /\ inFlight' = inFlight - 1
               /\ UNCHANGED timeVars
              
DeliverAndDropAck == /\ PathModelIsEnabled
                     /\ DROP_ACK
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
           
Fairness == /\ time!Fairness
            /\ SF_vars(DeliverPacket)

Spec == Init /\ [][Next]_vars /\ Fairness

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

NextTest == \/ Next
            \/ InjectPackets
            
FairnessTest == /\ time!Fairness
                /\ SF_vars(DeliverPacket)
                /\ SF_vars(InjectPackets)

SpecTest == Init /\ [][NextTest]_vars /\ FairnessTest  

Termination == time!Termination

=============================================================================
\* Modification History
\* Last modified Tue Nov 01 21:11:59 IRST 2022 by Arvin
\* Created Thu Oct 27 00:16:46 IRST 2022 by Arvin

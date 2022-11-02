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

(***************************************************************************)
(* When the link contains more than 't*C' packets, excessive packets WILL  *)
(* be dropped immediately, but triggering a timeout and then dropping the  *)
(* number of packets to 't*C'.                                             *)
(*                                                                         *)
(* Certain buffering strategies can be employed here to help, as well as   *)
(* some token bucket filters, but we will not implement that yet.          *)
(***************************************************************************)
                      
ExcessivePacketDropIsEnabled == /\ inFlight > t * C

(***************************************************************************)
(* At the end of each timestep, the path model may accept new packets into *)
(* the link as inflight packets.                                           *)
(***************************************************************************)
                      
PacketInjectionIsEnabled == /\ ticked = 1
                            /\ Finished = FALSE
                            
(***************************************************************************)
(* Path model is only enabled at the start of each timestep.  Before it    *)
(* procedes to take actions per packet, it check whether or not excessive  *)
(* packets are present.  If so, the packets will be dropped.               *)
(***************************************************************************)
        
PathModelIsEnabled == /\ inFlight > 0
                      /\ ticked = 0
                      /\ Finished = FALSE
                      /\ ~ExcessivePacketDropIsEnabled
                      
\* Deliver packets and return ACKs

DeliverPacket == /\ PathModelIsEnabled
                 /\ timeout' = 0
                 /\ nAck' = nAck + 1
                 /\ inFlight' = inFlight - 1
                 /\ UNCHANGED timeVars
                 
\* Deliver and return ACK, but trigger timeout
                 
DeliverLate == /\ PathModelIsEnabled 
               /\ timeout' = 1
               /\ nAck' = nAck + 1
               /\ inFlight' = inFlight - 1
               /\ UNCHANGED timeVars
               
\* Deliver the packet, but trigger timeout by dropping an ACK. 
\* Can be disabled completely
              
DeliverAndDropAck == /\ PathModelIsEnabled
                     /\ DROP_ACK
                     /\ timeout' = 1
                     /\ nAck' = nAck
                     /\ inFlight' = inFlight - 1
                     /\ UNCHANGED timeVars
                     
\* Drop the packet completely and trigger timeout
                     
DropCompletely == /\ PathModelIsEnabled
                  /\ timeout' = 1
                  /\ nAck' = nAck
                  /\ inFlight' = inFlight - 1
                  /\ UNCHANGED timeVars
                  
\* Drop packets exceeding the link capacity
                  
DropExcess == /\ ExcessivePacketDropIsEnabled
              /\ timeout' = 1
              /\ inFlight' = t * C
              /\ UNCHANGED <<timeVars, nAck>>
                  
Next == \/ DeliverPacket
        \/ DeliverLate
        \/ DeliverAndDropAck
        \/ DropCompletely
        \/ DropExcess
        \/ /\ ~ExcessivePacketDropIsEnabled
           /\ time!Next
           /\ UNCHANGED pathVars
           
\* Packet deliverance must remain strongly fair to prevent useless
\* scenarios.
           
Fairness == /\ time!Fairness
            /\ SF_vars(DeliverPacket)

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Always either:                                                          *)
(*     1) The link utility is less than or equal to 1                      *)
(*     2) We are at the start of taking actions per packet, which means    *)
(*        that if link utility is larger than 1, it will be immediately    *)
(*        corrected.                                                       *)
(***************************************************************************)

RateLimited == [] (inFlight <= t * C \/ ticked = 0)

(***************************************************************************)
(* To test the specification, we create another spec on top of the spec    *)
(* above.  This specification will allow for packet injections of random   *)
(* values and if everything goes well, the invariants must remain true.    *)
(***************************************************************************)

Max(a, b) == IF a > b THEN a ELSE b

newPacketsAllowed(timePassed, existingPackets) == Max(timePassed*MAX_ARRIVAL - existingPackets - 1, 0)

getRandomArrival(timePassed, existingPackets) == 
    RandomElement(0..newPacketsAllowed(timePassed, existingPackets))

InjectPackets == /\ PacketInjectionIsEnabled
                 /\ inFlight' = inFlight + getRandomArrival(t, inFlight)
                 /\ nAck' = nAck
                 /\ timeout' = timeout
                 /\ time!DoTick

NextTest == \/ Next
            \/ InjectPackets
            
(***************************************************************************)
(* For the same reason that delivering packets must be strongly fair,      *)
(* having packets to deliver in the first place must also be strongly      *)
(* fair!                                                                   *)
(***************************************************************************)
            
FairnessTest == /\ time!Fairness
                /\ SF_vars(DeliverPacket)
                /\ SF_vars(InjectPackets)

SpecTest == Init /\ [][NextTest]_vars /\ FairnessTest  

(***************************************************************************)
(* Termination condition just to check we have not overriden the time      *)
(* module.                                                                 *)
(***************************************************************************)

Termination == time!Termination

=============================================================================
\* Modification History
\* Last modified Wed Nov 02 15:51:35 IRST 2022 by Arvin
\* Created Thu Oct 27 00:16:46 IRST 2022 by Arvin

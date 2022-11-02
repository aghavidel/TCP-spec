-------------------------------- MODULE Reno --------------------------------
EXTENDS TLC, Sequences, Integers

CONSTANT C, MAX_T, MAX_ARRIVAL, DROP_ACK, SSTHRESH_START, MAX_WINDOW
VARIABLES t, ticked, nAck, inFlight, timeout, arrivals, cwnd, ssthresh

timeVars == <<t, ticked>>
pathVars == <<nAck, inFlight, timeout>>
tcpVars == <<arrivals, cwnd, ssthresh>>
vars == <<t, ticked, nAck, inFlight, timeout, arrivals, cwnd, ssthresh>>

time == INSTANCE Time WITH t <- t, ticked <- ticked, MAX_T <- MAX_T

path == INSTANCE SimplePathModel WITH nAck <- nAck, inFlight <- inFlight, timeout <- timeout,
                                      C <- C, MAX_ARRIVAL <- MAX_ARRIVAL, DROP_ACK <- DROP_ACK 
        
ASSUME /\ SSTHRESH_START > 1
       /\ MAX_WINDOW > SSTHRESH_START
       /\ MAX_T > 2

TypeOK == /\ path!TypeOK
          /\ arrivals \in Nat
          /\ arrivals \geq 0
          /\ cwnd \in Nat
          /\ cwnd \geq 1
          /\ ssthresh \in Nat
          /\ ssthresh \geq 2

Termination == path!Termination

Finished == path!Finished

RateLimited == path!RateLimited

Init == /\ path!Init
        /\ arrivals = 0
        /\ cwnd = 1
        /\ ssthresh = SSTHRESH_START
        
EnableIncreaseWindow == /\ timeout = 0
                        /\ cwnd < MAX_WINDOW
                        /\ IF cwnd < ssthresh 
                              THEN nAck > 0
                              ELSE nAck >= cwnd
                        /\ Finished = FALSE
\*                        /\ ticked = 0
                            
IncreaseWindow == /\ EnableIncreaseWindow
                  /\ IF cwnd < ssthresh
                        THEN /\ cwnd' = 2 * cwnd
                             /\ nAck' = nAck - 1
                        ELSE /\ nAck' = nAck - cwnd
                             /\ cwnd' = cwnd + 1
                  /\ UNCHANGED <<ssthresh, timeout, inFlight, arrivals, t, ticked>>
                  
EnableDecreaseWindow == /\ timeout = 1
                        /\ Finished = FALSE
\*                        /\ ticked = 0
                             
DecreaseWindow == /\ EnableDecreaseWindow
                  /\ IF cwnd >= 4
                        THEN ssthresh' = cwnd \div 2
                        ELSE ssthresh' = 2
                  /\ IF cwnd < ssthresh
                        THEN /\ cwnd' = 1
                        ELSE /\ cwnd' = cwnd \div 2
                  /\ timeout' = 0
                  /\ nAck' = 0
                  /\ UNCHANGED <<inFlight, arrivals, t, ticked>>
                  
EnableSendNewPacket == /\ timeout = 0
                       /\ arrivals > 0
                       /\ inFlight < cwnd
                       /\ Finished = FALSE
\*                       /\ ticked = 0
                    
SendNewPacket == /\ EnableSendNewPacket
                 /\ arrivals' = arrivals - 1
                 /\ inFlight' = inFlight + 1
                 /\ UNCHANGED <<nAck, timeout, cwnd, ssthresh, t, ticked>>
                 
Max(a, b) == IF a > b THEN a ELSE b

Min(a, b) == IF a < b THEN a ELSE b

newPacketsAllowed(timePassed, existingPackets) == Max(timePassed*C - existingPackets - 1, 0)

getRandomArrival(timePassed, existingPackets) == 
    RandomElement(0..Min(MAX_ARRIVAL, newPacketsAllowed(timePassed, existingPackets)))
                 
EnablePacketArrival == /\ ticked = 1
                       /\ Finished = FALSE
                       
PacketArrival == /\ EnablePacketArrival
                 /\ arrivals' = arrivals + getRandomArrival(t, inFlight)
                 /\ time!DoTick
                 /\ UNCHANGED (pathVars \o <<cwnd, ssthresh>>)
                 
Next == \/ IncreaseWindow
        \/ DecreaseWindow
        \/ SendNewPacket
        \/ PacketArrival
        \/ /\ path!Next
           /\ UNCHANGED tcpVars
           
Fairness == /\ path!Fairness
            /\ SF_vars(PacketArrival)

Spec == Init /\ [][Next]_vars /\ Fairness
                       
=============================================================================
\* Modification History
\* Last modified Wed Nov 02 15:39:06 IRST 2022 by Arvin
\* Created Mon Oct 31 01:51:50 IRST 2022 by Arvin

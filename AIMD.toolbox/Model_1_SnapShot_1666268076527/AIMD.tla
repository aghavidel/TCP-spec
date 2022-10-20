-------------------------------- MODULE AIMD --------------------------------

EXTENDS Integers, TLC, Sequences


CONSTANTS SSTHRESH_START, MAX_WINDOW, NUM_PACKETS
VARIABLES cwnd, timeout, nAck, inFlight, nPacket, ssthresh

vars == <<cwnd, timeout, nAck, inFlight, nPacket, ssthresh>>

ASSUME /\ SSTHRESH_START > 1
       /\ MAX_WINDOW > SSTHRESH_START
       /\ NUM_PACKETS > 0

TypeOK == /\ cwnd \in Nat
          /\ cwnd >= 1
          /\ timeout \in 0..1
          /\ nAck \in Nat
          /\ nAck >= 0
          /\ inFlight \in Nat
          /\ inFlight >= 0
          /\ nPacket \in Nat
          /\ nPacket >= 0
          
Init == /\ cwnd = 1
        /\ timeout = 0
        /\ nAck = 0
        /\ inFlight = 0
        /\ nPacket = NUM_PACKETS
        /\ ssthresh = SSTHRESH_START
        
CanIncreaseWindow == /\ timeout = 0
                     /\ cwnd < MAX_WINDOW
                     /\ IF cwnd < ssthresh 
                            THEN nAck > 0
                            ELSE nAck >= cwnd
                            
IncreaseWindow == /\ CanIncreaseWindow
                  /\ IF cwnd < ssthresh
                        THEN /\ cwnd' = 2 * cwnd
                             /\ nAck' = nAck - 1
                        ELSE /\ nAck' = nAck - cwnd
                             /\ cwnd' = cwnd + 1
                  /\ UNCHANGED <<ssthresh, timeout, inFlight, nPacket>>
                             
DecreaseWindow == /\ timeout = 1
                  /\ IF cwnd >= 4
                        THEN ssthresh' = cwnd \div 2
                        ELSE ssthresh' = 2
                  /\ IF cwnd < ssthresh
                        THEN /\ cwnd' = 1
                        ELSE /\ cwnd' = cwnd \div 2
                  /\ timeout' = 0
                  /\ nAck' = 0
                  /\ UNCHANGED <<inFlight, nPacket>>
                        
CanSendNewPacket == /\ timeout = 0
                    /\ nPacket > 0
                    /\ inFlight < cwnd
                    
SendNewPacket == /\ CanSendNewPacket
                 /\ nPacket' = nPacket - 1
                 /\ inFlight' = inFlight + 1
                 /\ UNCHANGED <<nAck, timeout, cwnd, ssthresh>>
                 
PathModelIsEnabled == inFlight > 0
                 
DeliverPacket == /\ PathModelIsEnabled
                 /\ timeout' = 0
                 /\ nAck' = nAck + 1
                 /\ inFlight' = inFlight - 1
                 /\ UNCHANGED <<nPacket, cwnd, ssthresh>>
                 
DeliverLate == /\ PathModelIsEnabled 
               /\ timeout' = 1
               /\ nAck' = nAck + 1
               /\ inFlight' = inFlight - 1
               /\ UNCHANGED <<nPacket, cwnd, ssthresh>>
              
DeliverAndDropAck == /\ PathModelIsEnabled
                     /\ timeout' = 1
                     /\ inFlight' = inFlight - 1
                     /\ UNCHANGED <<nPacket, cwnd, ssthresh, nAck>>
                     
DropCompletely == /\ PathModelIsEnabled
                  /\ timeout' = 1
                  /\ UNCHANGED <<nPacket, cwnd, ssthresh, nAck, inFlight>>
                  
Next == \/ SendNewPacket
        \/ IncreaseWindow
        \/ DecreaseWindow
        \/ DeliverPacket
        \/ DeliverLate
        \/ DeliverAndDropAck
        \/ DropCompletely
        
Spec == Init /\ [][Next]_vars /\ WF_vars(SendNewPacket) /\ SF_vars(DeliverPacket) /\ WF_vars(DecreaseWindow)


FinishedSending == /\ nPacket = 0
                   /\ inFlight = 0

Liveness == <>(FinishedSending)

=============================================================================
\* Modification History
\* Last modified Thu Oct 20 15:44:22 IRST 2022 by Arvin
\* Created Thu Sep 22 01:24:28 IRST 2022 by Arvin

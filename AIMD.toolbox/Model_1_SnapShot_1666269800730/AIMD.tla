-------------------------------- MODULE AIMD --------------------------------

EXTENDS Integers, TLC, Sequences

(*********************************************************)
(* The spec is parametrized with the following           *)
(*      SSTHRESH_START: Initial value of the Slow-Start  *)
(*                      threshold                        *)
(*      MAX_WINDOW: Maximum possible value of the        *)
(*                  congestion window                    *)
(*      NUM_PACKETS: Number of packets to send           *)
(*********************************************************)
                    

CONSTANTS SSTHRESH_START, MAX_WINDOW, NUM_PACKETS

(*********************************************************)
(* For variables, we introduce the following:            *)
(*      cwnd: The current TCP congestion window          *)
(*      timeout: Whether or not a timeout is triggered   *)
(*      nAck: Number of collected ACKs                   *)
(*      inFlight: Number of outstanding packets          *)
(*      nPacket: Number of packets to send               *)
(*      ssthresh: Slow-Start threshold                   *)
(*********************************************************)  

VARIABLES cwnd, timeout, nAck, inFlight, nPacket, ssthresh

vars == <<cwnd, timeout, nAck, inFlight, nPacket, ssthresh>>

(*********************************************************)
(*        These assumptions are merely for safety        *)
(*********************************************************)

ASSUME /\ SSTHRESH_START > 1
       /\ MAX_WINDOW > SSTHRESH_START
       /\ NUM_PACKETS > 0
       
(*********************************************************)
(*               The usual TypeOK invariant              *)
(*********************************************************)

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
        
(*********************************************************)
(* The window can be increased if and only if either     *)
(*      We are in Slow-Start and have received an ACK    *)
(*      We are in Congestion-Avoidance and have received *)
(*      at least a whole window-worth of ACKs            *)
(* All of these are subjected to no timeout happenning   *)
(*********************************************************)
        
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
                            
(*********************************************************)
(* The window can be decreased if and only if a timeout  *)
(* has happened (in Reno, there is also duplicate ACKs,  *)
(* we'll add it later                                    *)
(*********************************************************)

ShouldDecreaseWindow == timeout = 1
                             
DecreaseWindow == /\ ShouldDecreaseWindow
                  /\ IF cwnd >= 4
                        THEN ssthresh' = cwnd \div 2
                        ELSE ssthresh' = 2
                  /\ IF cwnd < ssthresh
                        THEN /\ cwnd' = 1
                        ELSE /\ cwnd' = cwnd \div 2
                  /\ timeout' = 0
                  /\ nAck' = 0
                  /\ UNCHANGED <<inFlight, nPacket>>
                            
(*********************************************************)
(* New packets can be sent if and only if:               *)
(*      1. A timeout has not occurred                    *)
(*      2. There is actually something to send           *)
(*      3. The window has space                          *)
(*********************************************************)
                        
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
                     /\ nPacket' = nPacket + 1
                     /\ UNCHANGED <<cwnd, ssthresh, nAck>>
                     
DropCompletely == /\ PathModelIsEnabled
                  /\ timeout' = 1
                  /\ nPacket' = nPacket + 1
                  /\ inFlight' = inFlight - 1
                  /\ UNCHANGED <<cwnd, ssthresh, nAck>>
                  
Next == \/ SendNewPacket
        \/ IncreaseWindow
        \/ DecreaseWindow
        \/ DeliverPacket
        \/ DeliverLate
        \/ DeliverAndDropAck
        \/ DropCompletely
        
Spec == Init /\ [][Next]_vars 
             /\ WF_vars(SendNewPacket) 
             /\ SF_vars(DeliverPacket) 
             /\ WF_vars(DecreaseWindow)


FinishedSending == /\ nPacket = 0
                   /\ inFlight = 0

Liveness == <>(FinishedSending)

=============================================================================
\* Modification History
\* Last modified Thu Oct 20 16:13:03 IRST 2022 by Arvin
\* Created Thu Sep 22 01:24:28 IRST 2022 by Arvin

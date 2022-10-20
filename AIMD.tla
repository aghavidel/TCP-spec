-------------------------------- MODULE AIMD --------------------------------

EXTENDS Integers, TLC, Sequences

(************************************************************)
(* The spec is parametrized with the following:             *)
(*      1. SSTHRESH_START: Initial value of the Slow-Start  *)
(*                         threshold                        *)
(*      2. MAX_WINDOW: Maximum possible value of the        *)
(*                     congestion window                    *)
(*      3. NUM_PACKETS: Number of packets to send           *)
(************************************************************)
                    

CONSTANTS SSTHRESH_START, MAX_WINDOW, NUM_PACKETS

(************************************************************)
(* For variables, we introduce the following:               *)
(*      1. cwnd: The current TCP congestion window          *)
(*      2. timeout: Whether or not a timeout is triggered   *)
(*      3. nAck: Number of collected ACKs                   *)
(*      4. inFlight: Number of outstanding packets          *)
(*      5. nPacket: Number of packets to send               *)
(*      6. ssthresh: Slow-Start threshold                   *)
(************************************************************)  

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
        
(************************************************************)
(* The window can be increased if and only if either:       *)
(*      1. We are in Slow-Start and have received an ACK    *)
(*      2. We are in Congestion-Avoidance and have received *)
(*         at least a whole window-worth of ACKs            *)
(* All of these are subjected to no timeout happenning      *)
(************************************************************)
        
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
                            
(*********************************************************)
(* The path model can arbitrarily decide for each packet *)
(* whether or not it gets delayed, dropped or delivered. *)
(* The ACKs can also exhibit the same behaviors.         *)
(*                                                       *)
(* These behaviors are enabled only if there is at least *)
(* one outstanding packet.                               *)
(*********************************************************)
                 
PathModelIsEnabled == inFlight > 0

                            
(*************************************************************)
(* In brief:                                                 *)
(*      1. DeliverPacket: Delivers the packet in time, so no *)
(*                        timeout happens and returns the an *)
(*                        ACK to the TCP.                    *)
(*      2. DeliverLate: The packet and the ACK are delivered *)
(*                      and thus the TCP timeouts and the    *)
(*                      window is decreased.                 *)
(*      3. DeliverAndDropAck: Packet is delivered but the    *)  
(*                            ACK is dropped. TCP is forced  *)
(*                            to retransmit. Retransmits are *)
(*                            simulated by magically adding  *)
(*                            a new packet for TCP to send.  *)
(*      4. DropCompletely: This is like above, it will be    *) 
(*                         once we implement duplicate ACK   *)
(*                         detection.                        *)
(*************************************************************)
                 
DeliverPacket == /\ PathModelIsEnabled
                 /\ timeout' = 0
                 /\ nAck' = nAck + 1
                 /\ inFlight' = inFlight
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
                            
(***********************************************************)
(* Some fairness specification is needed to prevent the    *) 
(* the path model from creating useless behaviors.         *)
(*      1. Weak fairness must hold for SendNewPacket. This *)
(*         prevents behaviors where TCP just stands there  *)
(*         and refuses to do anything.                     *)     
(*      2. Strong fairness is needed for DeliverPacket,    *)
(*         if not, we end up with extremely adversarial    *)
(*         behaviors from the path that just force TCP     *)
(*         into a retransmission loop.                     *)
(*      3. Weak fairness must hold for DecreaseWindow.     *)
(*         This is a consequence of how I wrote this code. *)
(*         Without this, TCP can once again just stand     *)
(*         there and refuse to send anything once a        *)
(*         timeout happenes. This prevents that.           *)
(***********************************************************)
        
Spec == Init /\ [][Next]_vars 
             /\ WF_vars(SendNewPacket) 
             /\ SF_vars(DeliverPacket) 
             /\ WF_vars(DecreaseWindow)

(**************************************************************)
(* The least that TCP should do is to actually manage to send *)
(* things!                                                    *)
(**************************************************************)

FinishedSending == /\ nPacket = 0
                   /\ inFlight = 0

Liveness == <>(FinishedSending)

=============================================================================
\* Modification History
\* Last modified Thu Oct 20 16:43:31 IRST 2022 by Arvin
\* Created Thu Sep 22 01:24:28 IRST 2022 by Arvin

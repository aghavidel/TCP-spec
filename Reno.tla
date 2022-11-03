-------------------------------- MODULE Reno --------------------------------
(***************************************************************************)
(* Implements simple AIMD TCP protocol.  It can use any pthe model,        *)
(* provided that it implements the specification of SimplePathModel.       *)
(***************************************************************************)

EXTENDS TLC, Sequences, Integers

(***************************************************************************)
(* MAX_ARRIVAL    : The rate at which packets can arrive.                  *)
(*                  Helps lower runtime.                                   *)
(* SSTHRESSH_START: Starting value of Slow-Start Threshold.                *)
(* MAX_WINDOW     : Maximum allowed value of cwnd.                         *)
(*                                                                         *)
(* added          : The number of packets arriving.                        *)
(* arrivals       : Total number of packets arrived.                       *)
(* buffered       : Number of packets buffered for service.                *)
(* cwnd           : Congestion window.                                     *)
(* ssthresh       : Slow-Start threshold                                   *)
(***************************************************************************)

CONSTANT C, MAX_T, MAX_ARRIVAL, DROP_ACK, SSTHRESH_START, MAX_WINDOW
VARIABLES t, ticked, 
          nAck, inFlight, timeout, 
          added, arrivals, buffered, cwnd, ssthresh

timeVars == <<t, ticked>>
pathVars == <<nAck, inFlight, timeout>>
tcpVars == <<arrivals, buffered, cwnd, ssthresh, added>>
vars == <<t, ticked, nAck, inFlight, timeout, arrivals, added, buffered, cwnd, ssthresh>>

time == INSTANCE Time WITH t <- t, ticked <- ticked, MAX_T <- MAX_T

(***************************************************************************)
(* Here, "SimplePathModel" is used. Any other path model used must         *)
(* implement:                                                              *)
(*     1) "ExcessivePacketDropIsEnabled": A boolean formula that specifies *)
(*        if path capacity has been exceeded. This MUST always trigger a   *)
(*        timeout and thus disables the TCP until that timeout happens.    *)
(*                                                                         *)
(*     2) "Init" and "Next" predicates.                                    *)
(*                                                                         *)
(*     3) "Fairness" for fairness conditions if required.                  *)
(*                                                                         *)
(*     4) Variables <<nAck, inFlight, timeout>> at the very least.         *)
(***************************************************************************)

path == INSTANCE SimplePathModel WITH nAck <- nAck, inFlight <- inFlight, timeout <- timeout,
                                      C <- C, MAX_ARRIVAL <- MAX_ARRIVAL, DROP_ACK <- DROP_ACK 
        
ASSUME /\ SSTHRESH_START > 1
       /\ MAX_WINDOW > SSTHRESH_START
       /\ MAX_T > 2
       
(***************************************************************************)
(* A note about "added":                                                   *)
(*                                                                         *)
(* "added" segnifies that some packets have arrived and should go into the *)
(* input buffer.  If added is nonzero, all TCP window actions are disabled *)
(* until we add the packets into the buffer.                               *)
(*                                                                         *)
(* This does not change the possible behaviors, but it helps prevent some  *)
(* repeated states when those packets need to be sent.                     *)
(***************************************************************************)

TypeOK == /\ path!TypeOK
          /\ arrivals \in Nat
          /\ arrivals \geq 0
          /\ buffered \in Nat
          /\ buffered \geq 0
          /\ added \in Nat
          /\ added \geq 0
          /\ cwnd \in Nat
          /\ cwnd \geq 1
          /\ ssthresh \in Nat
          /\ ssthresh \geq 2
          
(***************************************************************************)
(* These are the 3 basic conditions that the specification must satisfy.   *)
(* It gurantees the safety of instantiated specifications.                 *)
(***************************************************************************)

Termination == path!Termination

Finished == path!Finished

RateLimited == path!RateLimited

Init == /\ path!Init
        /\ arrivals = 0
        /\ cwnd = 1
        /\ ssthresh = SSTHRESH_START
        /\ buffered = 0
        /\ added = 0
        
(***************************************************************************)
(* EnableIncreaseWindow:                                                   *)
(*                                                                         *)
(* Only enabled when no timeout has happened and we have not exceeded      *)
(* MAX_WINDOW.  If still in slow-start, one ACK at least should be         *)
(* present, if during congestion avoidance, we need a whole cwnd worth of  *)
(* acks to increase the window.                                            *)
(*                                                                         *)
(* IncreaseWindow:                                                         *)
(*                                                                         *)
(* The action itself doubles cwnd if during slow-start or adds one to it   *)
(* if during congestion avoidance.  Appropriate amounts of ACKs are        *)
(* consumed as well ...                                                    *)
(***************************************************************************)
                
EnableIncreaseWindow == /\ timeout = 0
                        /\ cwnd < MAX_WINDOW
                        /\ IF cwnd < ssthresh 
                              THEN nAck > 0
                              ELSE nAck >= cwnd
                        /\ Finished = FALSE
                        /\ ~path!ExcessivePacketDropIsEnabled
                        /\ added = 0

IncreaseWindow == /\ EnableIncreaseWindow
                  /\ IF cwnd < ssthresh
                        THEN /\ cwnd' = 2 * cwnd
                             /\ nAck' = nAck - 1
                        ELSE /\ nAck' = nAck - cwnd
                             /\ cwnd' = cwnd + 1
                  /\ UNCHANGED <<ssthresh, timeout, inFlight, added, arrivals, buffered, t, ticked>>
                  
(***************************************************************************)
(* EnableDecreaseWindow:                                                   *)
(*                                                                         *)
(* Only enabled during timeouts.                                           *)
(*                                                                         *)
(* DecreaseWindow:                                                         *)
(*                                                                         *)
(* It resets the number of received ACKs, sets timeout to zero and cuts    *)
(* the window in half if slow-start is finished, else cwnd is set to 1.    *)
(* Half of current cwnd is added to slow-start threshold.                  *)
(***************************************************************************)
                  
EnableDecreaseWindow == /\ timeout = 1
                        /\ Finished = FALSE
                        /\ ~path!ExcessivePacketDropIsEnabled
                        /\ added = 0

DecreaseWindow == /\ EnableDecreaseWindow
                  /\ IF cwnd >= 4
                        THEN ssthresh' = cwnd \div 2
                        ELSE ssthresh' = 2
                  /\ IF cwnd < ssthresh
                        THEN /\ cwnd' = 1
                        ELSE /\ cwnd' = cwnd \div 2
                  /\ timeout' = 0
                  /\ nAck' = 0
                  /\ UNCHANGED <<inFlight, added, arrivals, buffered, t, ticked>>
                                            
Max(a, b) == IF a > b THEN a ELSE b

newPacketsAllowed(timePassed, packetsArrived) == Max(
    timePassed * MAX_ARRIVAL - packetsArrived - 1, 0
)

getRandomArrival(timePassed, packetsArrived) == RandomElement(
    0..newPacketsAllowed(timePassed, packetsArrived)
)

(***************************************************************************)
(* PacketAcceptIsEnabled:                                                  *)
(*                                                                         *)
(* Enabled only when timeout is zero and we have not exceeded the maximum  *)
(* arrival rate yet.                                                       *)
(*                                                                         *)
(* AcceptPackets:                                                          *)
(*                                                                         *)
(* Draws a random number of packets up to a maximum value that gurantees   *)
(* arrival rate is not exceeded, and assigns it to "added". If there are   *)
(* packets to add, all TCP actions are disabled until these new packets    *)
(* are added to the input buffer.                                          *)
(***************************************************************************)

PacketAcceptIsEnabled == /\ ticked = 0
                         /\ timeout = 0
                         /\ Finished = FALSE
                         /\ (t * MAX_ARRIVAL - arrivals) > 0
                         /\ ~path!ExcessivePacketDropIsEnabled

AcceptPackets == /\ PacketAcceptIsEnabled
                 /\ added' = getRandomArrival(t, arrivals)
                 /\ UNCHANGED <<t, ticked, nAck, inFlight, timeout, cwnd, ssthresh, 
                    arrivals, buffered>>
                    
(***************************************************************************)
(* PacketArrivalIsEnabled:                                                 *)
(*                                                                         *)
(* Only enabled when added is non-zero and the rest of packet acceptance   *)
(* conditions also hold.                                                   *)
(*                                                                         *)
(* PacketArrival:                                                          *)
(*                                                                         *)
(* Adds the value of "added" to total arrivals and buffered values, and    *)
(* then resets "added" to zero, enabling furthur TCP actions.              *)
(***************************************************************************)
                    
PacketArrivalIsEnabled == /\ added > 0
                          /\ PacketAcceptIsEnabled

PacketArrival == /\ PacketArrivalIsEnabled
                 /\ arrivals' = arrivals + added
                 /\ buffered' = buffered + added
                 /\ added' = 0
                 /\ UNCHANGED <<t, ticked, nAck, inFlight, timeout, cwnd, ssthresh>>
                 
(***************************************************************************)
(* PacketSendIsEnabled:                                                    *)
(*                                                                         *)
(* Only enabled when there are buffered packets to deliver and             *)
(* inFlight < cwnd, meaning that the window has empty space.               *)
(*                                                                         *)
(* SendNewPackets:                                                         *)
(*                                                                         *)
(* If there are enough buffered packets, the window is filled completely,  *)
(* if not, the window is filled until the buffer is empty.                 *)
(***************************************************************************)

PacketSendIsEnabled == /\ ticked = 0
                       /\ Finished = FALSE
                       /\ buffered > 0
                       /\ inFlight < cwnd
                       /\ timeout = 0
                       /\ ~path!ExcessivePacketDropIsEnabled
                       /\ added = 0
                     
SendNewPackets == /\ PacketSendIsEnabled
                  /\ IF cwnd - inFlight > buffered
                        THEN /\ inFlight' = inFlight + buffered
                             /\ buffered = 0
                        ELSE /\ buffered' = buffered - (cwnd - inFlight)  
                             /\ inFlight' = cwnd 
                  /\ UNCHANGED <<t, ticked, nAck, timeout, cwnd, added, ssthresh, arrivals>>

Next == \/ IncreaseWindow
        \/ DecreaseWindow
        \/ SendNewPackets
        \/ AcceptPackets
        \/ PacketArrival
        \/ /\ path!Next
           /\ UNCHANGED tcpVars
           
Fairness == /\ path!Fairness

Spec == Init /\ [][Next]_vars /\ Fairness                       
=============================================================================
\* Modification History
\* Last modified Thu Nov 03 03:35:21 IRST 2022 by Arvin
\* Created Mon Oct 31 01:51:50 IRST 2022 by Arvin

-------------------------------- MODULE Time --------------------------------
(***************************************************************************)
(* This model implements discrete timesteps for other modules.             *)
(***************************************************************************)

EXTENDS Integers, TLC, Sequences

(***************************************************************************)
(* MAX_T: The maximum value of the timer variable 't'.                     *)
(* t:     The timer variable, monotonically increasing during execution.   *)
(* ticked:Asserts whether or not this time interval is consumed, meaning   *)
(*        that it can be used to disable all actions tied to the module.   *)
(***************************************************************************)

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

(***************************************************************************)
(* In order to prevent deadlocks in the timer, weak fairness must hold for *)
(* all time actions, meaning that if continuously enabled, they SHOULD be  *)
(* executed It is not hard to see that weak and strong fairness are        *)
(* equivalent in this model.                                               *)
(***************************************************************************)

Fairness == WF_vars(DoTick) /\ WF_vars(ConsumeInterval)
        
Spec == /\ Init 
        /\ [][Next]_vars 
        /\ Fairness

(***************************************************************************)
(* Of course, we expect the timer to finish and disable all actions after  *)
(* we reach 'MAX_T'.  This can lead to deadlocks when used in other        *)
(* modules, so you might have to uncheck the 'deadlock' property in TLC.   *)
(***************************************************************************)

Termination == <>(Finished = TRUE)

=============================================================================
\* Modification History
\* Last modified Tue Nov 01 21:01:33 IRST 2022 by Arvin
\* Created Tue Oct 25 23:09:31 IRST 2022 by Arvin

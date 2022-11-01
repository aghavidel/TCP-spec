-------------------------- MODULE GeneralPathModel --------------------------
EXTENDS TLC, Integers, Sequences

CONSTANTS MAX_T, C, MIN_BUFF, MAX_BUFF, MAX_ARRIVAL
VARIABLES t, ticked, arrival, service, loss, timeout

timeVars == <<t, ticked>>
pathVars == <<arrival, service, loss, timeout>>
vars == timeVars \o pathVars

arrival_list == <<>>
service_list == <<>>
loss_list == <<>>

time == INSTANCE Time WITH t <- t, ticked <- ticked 

TypeOK == /\ time!TypeOK
          /\ arrival \in Nat
          /\ arrival \geq 0
          /\ service \in Nat
          /\ service \geq 0
          /\ loss \in Nat
          /\ loss \geq 0
          /\ timeout \in 0..1
          /\ arrival_list \in Seq(Nat \X Nat)
          /\ service_list \in Seq(Nat \X Nat)
          /\ loss_list \in Seq(Nat \X Nat)
          
ASSUME /\ MIN_BUFF \leq MAX_BUFF

Init == /\ time!Init
        /\ arrival = 0
        /\ service = 0
        /\ loss = 0
        /\ timeout = 0



=============================================================================
\* Modification History
\* Last modified Wed Nov 02 00:02:16 IRST 2022 by Arvin
\* Created Tue Nov 01 21:31:06 IRST 2022 by Arvin

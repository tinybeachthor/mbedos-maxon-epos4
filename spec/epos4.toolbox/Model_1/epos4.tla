------------------------------- MODULE epos4 -------------------------------

\******
\* Possible NMT states
\******
CONSTANT NMT_Booting, NMT_PreOperational, NMT_Operational, NMT_Stopped

NMT == {NMT_Booting, NMT_PreOperational, NMT_Operational, NMT_Stopped}

-----

VARIABLES nmt_state, nmt_requested

vars == <<nmt_state, nmt_requested>>

-----

TypeOK == /\ nmt_state \in NMT
          /\ nmt_requested \in NMT

-----

\******
\* Received a BootUp message
\******
NMT_BootUp == /\ nmt_state = NMT_Booting
               /\ nmt_state' = NMT_PreOperational
               /\ UNCHANGED nmt_requested

\******
\* State transmition confirmation
\******
NMT_Transition_Confirmed == /\ nmt_state /= nmt_requested
                            /\ nmt_state' = nmt_requested
                            /\ UNCHANGED nmt_requested

\******
\* Request state transitions
\******
NMT_EnterPreOperational == /\ \/ nmt_state = NMT_Operational
                              \/ nmt_state = NMT_Stopped
                           /\ nmt_requested = nmt_state
                           /\ nmt_requested' = NMT_PreOperational
                           /\ UNCHANGED nmt_state

NMT_ResetCommunication == /\ \/ nmt_state = NMT_Operational
                             \/ nmt_state = NMT_PreOperational
                             \/ nmt_state = NMT_Stopped
                          /\ nmt_requested = nmt_state
                          /\ nmt_requested' = NMT_Booting
                          /\ UNCHANGED nmt_state

NMT_ResetNode == /\ \/ nmt_state = NMT_Operational
                    \/ nmt_state = NMT_PreOperational
                    \/ nmt_state = NMT_Stopped
                 /\ nmt_requested = nmt_state
                 /\ nmt_requested' = NMT_Booting
                 /\ UNCHANGED nmt_state

NMT_StartRemoteNode == /\ \/ nmt_state = NMT_PreOperational
                          \/ nmt_state = NMT_Stopped
                       /\ nmt_requested = nmt_state
                       /\ nmt_requested' = NMT_Operational
                       /\ UNCHANGED nmt_state

NMT_StopRemoteNode == /\ \/ nmt_state = NMT_Operational
                         \/ nmt_state = NMT_PreOperational
                      /\ nmt_requested = nmt_state
                      /\ nmt_requested' = NMT_Stopped
                      /\ UNCHANGED nmt_state

-----

Init == /\ nmt_state = NMT_Booting
        /\ nmt_requested = NMT_PreOperational

Next == \/ NMT_BootUp
        \/ NMT_Transition_Confirmed
        \/ \/ NMT_EnterPreOperational
           \/ NMT_ResetCommunication
           \/ NMT_ResetNode
           \/ NMT_StartRemoteNode
           \/ NMT_StopRemoteNode

Live == \A s \in NMT :
           (nmt_requested = s) ~> (nmt_state = s)
           
-----

Spec == Init /\ [][Next]_<<vars>> /\ WF_vars(Next)

=============================================================================
\* Modification History
\* Last modified Mon Jan 13 19:05:23 CET 2020 by martin
\* Created Mon Jan 13 12:39:13 CET 2020 by martin

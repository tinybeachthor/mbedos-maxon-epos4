------------------------------- MODULE epos4 -------------------------------

CONSTANT UNKNOWN

\* NMT states
CONSTANT NMT_Booting, NMT_PreOperational, NMT_Operational, NMT_Stopped

NMT == {NMT_Booting, NMT_PreOperational, NMT_Operational, NMT_Stopped}

-----

VARIABLES nmt_state
VARIABLES nmt_requested

-----

TypeOK == /\ nmt_state \in (NMT \cup UNKNOWN)

-----

Recv_BootUp == /\ nmt_state = NMT_Booting
               /\ nmt_state' = NMT_PreOperational
               /\ UNCHANGED nmt_requested

NMT_Transition_Confirmed == /\ nmt_state /= nmt_requested
                            /\ nmt_state' = nmt_requested
                            /\ UNCHANGED nmt_requested

NMT_EnterPreOperational == /\ \/ nmt_state = NMT_Operational
                              \/ nmt_state = NMT_Stopped
                           /\ nmt_requested = nmt_state
                           /\ nmt_requested' = NMT_PreOperational

NMT_ResetCommunication == /\ \/ nmt_state = NMT_Operational
                             \/ nmt_state = NMT_PreOperational
                             \/ nmt_state = NMT_Stopped
                          /\ nmt_requested = nmt_state
                          /\ nmt_requested' = NMT_Booting

NMT_ResetNode == /\ \/ nmt_state = NMT_Operational
                    \/ nmt_state = NMT_PreOperational
                    \/ nmt_state = NMT_Stopped
                 /\ nmt_requested = nmt_state
                 /\ nmt_requested' = NMT_Booting

NMT_StartRemoteNode == /\ \/ nmt_state = NMT_PreOperational
                          \/ nmt_state = NMT_Stopped
                       /\ nmt_requested = nmt_state
                       /\ nmt_requested' = NMT_Operational

NMT_StopRemoteNode == /\ \/ nmt_state = NMT_Operational
                         \/ nmt_state = NMT_PreOperational
                      /\ nmt_requested = nmt_state
                      /\ nmt_requested' = NMT_Stopped

-----

Init == /\ nmt_state = UNKNOWN
        /\ nmt_requested = NMT_Booting

Next == \/ Recv_BootUp
        \/ NMT_Transition_Confirmed
        \/ NMT_EnterPreOperational
        \/ NMT_ResetCommunication
        \/ NMT_ResetNode
        \/ NMT_StartRemoteNode
        \/ NMT_StopRemoteNode

Live == /\ \A s \in NMT :
              (nmt_requested = s) ~> (nmt_state = s)

=============================================================================
\* Modification History
\* Last modified Mon Jan 13 14:35:03 CET 2020 by martin
\* Created Mon Jan 13 12:39:13 CET 2020 by martin

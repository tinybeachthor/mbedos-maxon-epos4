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

Go_NMT_Operational == /\ nmt_state = NMT_Booting
                      /\ nmt_requested = nmt_state
                      /\ nmt_requested' = NMT_Operational

-----

Init == /\ nmt_state = UNKNOWN
        /\ nmt_requested = NMT_Booting

Next == \/ Recv_BootUp
        \/ NMT_Transition_Confirmed
        \/ Go_NMT_Operational

Live == /\ \A s \in NMT :
              (nmt_requested = s) ~> (nmt_state = s)

=============================================================================
\* Modification History
\* Last modified Mon Jan 13 14:35:03 CET 2020 by martin
\* Created Mon Jan 13 12:39:13 CET 2020 by martin

------------------------------- MODULE epos4 -------------------------------

\* NMT states
CONSTANT NMT_Booting, NMT_PreOperational, NMT_Operational, NMT_Stopped

NMT == {NMT_Booting, NMT_PreOperational, NMT_Operational, NMT_Stopped}

\* EPOS states
CONSTANT EPOS_NotReadyToSwitchOn, EPOS_SwitchOnDisabled, EPOS_ReadyToSwitchOn,
    EPOS_SwitchedOn, EPOS_OperationEnabled, EPOS_QuickStopActive,
    EPOS_FaultReactionActive, EPOS_Fault

EPOS == {EPOS_NotReadyToSwitchOn, EPOS_SwitchOnDisabled,
  EPOS_ReadyToSwitchOn, EPOS_SwitchedOn, EPOS_OperationEnabled,
  EPOS_QuickStopActive, EPOS_FaultReactionActive, EPOS_Fault}

-----

VARIABLES nmt_state, epos_state

-----

TypeOK == /\ nmt_state \in NMT
          /\ epos_state \in EPOS

-----

Recv_BootUp == /\ nmt_state = NMT_Booting
               /\ nmt_state' = NMT_PreOperational
               /\ UNCHANGED epos_state

-----

Init == /\ nmt_state = NMT_Booting
        /\ epos_state = EPOS_NotReadyToSwitchOn

Next == \/ Recv_BootUp

=============================================================================
\* Modification History
\* Last modified Mon Jan 13 13:50:35 CET 2020 by martin
\* Created Mon Jan 13 12:39:13 CET 2020 by martin

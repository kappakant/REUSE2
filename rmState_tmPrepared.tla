------------------------- MODULE rmState_tmPrepared -------------------------
CONSTANT RMs

VARIABLES rmState, tmPrepared

vars == <<rmState, tmPrepared>>

Init ==
    /\ rmState = [rm \in RMs |-> "working"]
    /\ tmPrepared = {}

SndPrepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    /\ UNCHANGED(tmPrepared)
    
SndCommit(rm) ==
    /\ tmPrepared = RMs
    /\ UNCHANGED(rmState)
    /\ UNCHANGED(tmPrepared)
    
RcvPrepare(rm) ==
    /\ tmPrepared' = tmPrepared \cup {rm}
    /\ UNCHANGED(rmState)
    
RcvCommit(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
    /\ UNCHANGED(tmPrepared)
    
RcvAbort(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED(tmPrepared)
    
SilentAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED(tmPrepared)
    
Next ==
    \E rm \in RMs:
        \/ SndPrepare(rm)
        \/ SndCommit(rm)
        \/ RcvPrepare(rm)
        \/ RcvCommit(rm)
        \/ RcvAbort(rm)
        \/ SilentAbort(rm)
        
Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
    /\ tmPrepared \in SUBSET RMs
    
Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")
=============================================================================
\* Modification History
\* Last modified Thu Jun 19 03:55:49 EDT 2025 by johnnguyen
\* Created Wed Jun 18 17:19:29 EDT 2025 by johnnguyen

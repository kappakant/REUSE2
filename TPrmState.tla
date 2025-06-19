----------------------------- MODULE TPrmState -----------------------------
CONSTANT RMs

VARIABLES rmState

vars == <<rmState>>

Init ==
    rmState = [rm \in RMs |-> "working"]
    
SndPrepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    
\* No RcvPrepare

\* No SndCommit

RcvCommit(rm) ==
    rmState' = [rmState EXCEPT ![rm] = "committed"]
    
\* No SndAbort

RcvAbort(rm) ==
    rmState' = [rmState EXCEPT ![rm] = "aborted"]
    
SilentAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    
Next ==
    \E rm in RMs:
        \/ SndPrepare(rm)
        \/ RcvCommit(rm)
        \/ RcvAbort(rm)
        \/ SilentAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
    
Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")

=============================================================================
\* Modification History
\* Last modified Wed Jun 18 17:21:21 EDT 2025 by johnnguyen
\* Created Sat Jun 14 15:07:32 EDT 2025 by johnnguyen

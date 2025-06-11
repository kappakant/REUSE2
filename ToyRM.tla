------------------------------- MODULE ToyRM -------------------------------
CONSTANT RMs

VARIABLES rmState

vars == <<rmState>>

Init == 
    rmState = [rm \in RMs |-> "working"]

Prepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]

Commit(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "commit"]
    
Abort(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]
    
SilentAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]

\* For the purposes of using carini
Next ==
    \E r \in RMs:
        \/ Prepare(r)
        \/ Commit(r)
        \/ Abort(r)
        \/ SilentAbort(r)

Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "abort" /\ rmState[rm2] = "commit")

Spec == Init /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Tue Jun 10 16:09:12 EDT 2025 by johnnguyen
\* Created Fri Jun 06 14:20:45 EDT 2025 by johnnguyen

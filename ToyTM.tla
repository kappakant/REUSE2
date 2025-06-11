------------------------------- MODULE ToyTM -------------------------------
CONSTANT RMs

VARIABLES tmState, tmPrepared

vars == <<tmState, tmPrepared>>

Init ==
    /\ tmState = "init"
    /\ tmPrepared = {}
    
Prepare(rm) ==
    /\ tmState = "init"
    /\ tmPrepared' = tmPrepared \cup {rm}
    /\ UNCHANGED(tmState)
    
Commit(rm) ==
    /\ tmState \in {"init", "commit"}
    /\ tmPrepared = RMs
    /\ tmState' = "commit"
    /\ UNCHANGED(tmPrepared)  

Abort(rm) ==
    /\ tmState \in {"init", "abort"}
    /\ tmState' = "abort"
    /\ UNCHANGED(tmPrepared)

\* For carini
Next ==
    \E r \in RMs:
        \/ Prepare(r)
        \/ Commit(r)
        \/ Abort(r)
        
Spec == Init /\ [][Next]_vars
=============================================================================
\* Modification History
\* Last modified Tue Jun 10 16:12:23 EDT 2025 by johnnguyen
\* Created Mon Jun 09 14:02:06 EDT 2025 by johnnguyen

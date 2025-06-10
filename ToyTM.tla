------------------------------- MODULE ToyTM -------------------------------
CONSTANT RMs

VARIABLES tmState, tmPrepared

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

Abort(rm)
    /\ tmState \in {"init", "abort"}
    /\ tmState' = "abort"
    /\ UNCHANGED(tmPrepared)

=============================================================================
\* Modification History
\* Last modified Mon Jun 09 18:48:21 EDT 2025 by johnnguyen
\* Created Mon Jun 09 14:02:06 EDT 2025 by johnnguyen

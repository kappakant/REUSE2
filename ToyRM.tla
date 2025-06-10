------------------------------- MODULE ToyRM -------------------------------
CONSTANT RMs

VARIABLES rmState

Init == 
    rmState = [rm \in RMs |-> "working"]

\* made X'[rm] = y more explicit since no TypeOK
Prepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    \*/\ rmState'[rm] = "prepared"

Commit(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "commit"]
    \*/\ rmState'[rm] = "commit"
    
Abort(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]
    \* /\ rmState'[rm] = "abort"
    
SilentAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "abort"]
    \*/\ rmState'[rm] = "abort"



=============================================================================
\* Modification History
\* Last modified Sun Jun 08 17:46:40 EDT 2025 by johnnguyen
\* Created Fri Jun 06 14:20:45 EDT 2025 by johnnguyen

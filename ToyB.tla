-------------------------------- MODULE ToyB --------------------------------
CONSTANT RMs

VARIABLES oncePrepare, onceCommit, onceAbort

\* Changed it a little bit because asserting this without or even with TypeOK was annoying
Init == 
    /\ oncePrepare = [rm \in RMs |-> FALSE]
    /\ onceCommit  = [rm \in RMs |-> FALSE]
    /\ onceAbort   = [rm \in RMs |-> FALSE]
    
Prepare(rm) ==
    /\ oncePrepare' = [oncePrepare EXCEPT ![rm] = TRUE]
    \*/\ oncePrepare'[rm] = TRUE
    /\ UNCHANGED(onceCommit)
    /\ UNCHANGED(onceAbort)
    
Commit(rm) ==
    /\ onceCommit' = [onceCommit EXCEPT ![rm] = TRUE]
    \*/\ onceCommit'[rm] = TRUE
    /\ UNCHANGED(oncePrepare)
    /\ UNCHANGED(onceAbort)
    
Abort(rm) ==
    /\ onceAbort' = [onceAbort EXCEPT ![rm] = TRUE]
    \*/\ onceAbort'[rm] = TRUE
    /\ UNCHANGED(oncePrepare)
    /\ UNCHANGED(onceCommit)

=============================================================================
\* Modification History
\* Last modified Mon Jun 09 15:04:29 EDT 2025 by johnnguyen
\* Created Fri Jun 06 14:20:11 EDT 2025 by johnnguyen

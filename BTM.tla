-------------------------------- MODULE BTM --------------------------------
CONSTANT RMs

VARIABLES oncePrepare, onceCommit, onceAbort
VARIABLES tmState, tmPrepared

B  == INSTANCE ToyB  WITH RMs <- RMs, oncePrepare <- oncePrepare, onceCommit <- onceCommit, onceAbort <- onceAbort
TM == INSTANCE ToyTM WITH RMs <- RMs, tmState <- tmState, tmPrepared <- tmPrepared

varsBTM ==
    <<oncePrepare, onceCommit, onceAbort,
      tmState, tmPrepared>>

varsB == <<oncePrepare, onceCommit, onceAbort>>
varsTM == <<tmState, tmPrepared>>

Init == B!Init /\ TM!Init

TypeOK ==
    /\ oncePrepare \in [RMs -> {FALSE, TRUE}]
    /\ onceCommit \in [RMs -> {FALSE, TRUE}]
    /\ onceAbort \in [RMs -> {FALSE, TRUE}]
    /\ tmState \in {"init", "commit", "abort"}
    /\ tmPrepared \in SUBSET RMs

SyncPrepare(rm) == B!Prepare(rm) /\ TM!Prepare(rm)
SyncCommit(rm)  == B!Commit(rm) /\ TM!Commit(rm)
SyncAbort(rm)   == B!Abort(rm) /\ TM!Abort(rm)

Next == \E rm \in RMs:
            \/ SyncPrepare(rm)
            \/ SyncCommit(rm)
            \/ SyncAbort(rm)
            
ToyR ==
    /\ (\E r \in RMs: onceCommit[r]) => (\A r \in RMs: oncePrepare[r])
    /\ (\E r \in RMs: onceAbort[r])  => (\A r \in RMs: ~onceCommit[r])
    
Itm == 
    /\ TypeOK
    
    /\ \A r \in RMs: r \in tmPrepared => oncePrepare[r]
    /\ tmState = "commit" => RMs = tmPrepared
    
    /\ (\E r \in RMs: onceCommit[r]) => tmState = "commit"
    
    /\ tmState = "abort" => (\A r \in RMs: ~onceCommit[r])
    /\ (\E r \in RMs: onceAbort[r]) => tmState = "abort"   

=============================================================================
\* Modification History
\* Last modified Tue Jun 10 15:46:08 EDT 2025 by johnnguyen
\* Created Mon Jun 09 14:04:54 EDT 2025 by johnnguyen

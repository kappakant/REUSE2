-------------------------------- MODULE RMB --------------------------------
CONSTANT RMs

VARIABLES rmState
VARIABLES oncePrepare, onceCommit, onceAbort

RM == INSTANCE ToyRM WITH RMs <- RMs, rmState <- rmState
B  == INSTANCE ToyB WITH RMs <- RMs, oncePrepare <- oncePrepare, onceCommit <- onceCommit, onceAbort <- onceAbort

varsRMB ==
    <<rmState, \* ToyRM 
    oncePrepare, onceCommit, onceAbort>> \*ToyB
    
varsB == <<oncePrepare, onceCommit, onceAbort>>
varsRM == <<rmState>>

Init == RM!Init /\ B!Init

TypeOK ==
    /\ oncePrepare \in [RMs -> {FALSE, TRUE}]
    /\ onceCommit \in [RMs -> {FALSE, TRUE}]
    /\ onceAbort \in [RMs -> {FALSE, TRUE}]
    /\ rmState \in [RMs -> {"working", "prepared", "commit", "abort"}]

\* So here's where stutter-stepping comes into play.
\* Wait, why was I enforcing stuttersteps here? 
SyncPrepare(rm)     == RM!Prepare(rm) /\ B!Prepare(rm)
SyncCommit(rm)      == RM!Commit(rm) /\ B!Commit(rm)
SyncAbort(rm)       == RM!Abort(rm) /\ B!Abort(rm)
SilentAbortRMB(rm)  == RM!SilentAbort(rm) /\ UNCHANGED(oncePrepare)
                                          /\ UNCHANGED(onceCommit)
                                          /\ UNCHANGED(onceAbort)

Next == 
    \E rm \in RMs: 
        \/ SyncPrepare(rm)
        \/ SyncCommit(rm)
        \/ SyncAbort(rm)
        \/ SilentAbortRMB(rm)
        
Consistent == \A r1, r2 \in RMs: ~(rmState[r1] = "abort" /\ rmState[r2] = "commit")   
        
ToyR == 
    /\ (\E r \in RMs: onceCommit[r]) => (\A r \in RMs: oncePrepare[r])
    /\ (\E r \in RMs: onceAbort[r])  => (\A r \in RMs: ~onceCommit[r])

Irm == 
    /\ Consistent
    /\ \A r \in RMs: onceCommit[r] <=> rmState[r] = "commit"
    /\ \A r \in RMs: oncePrepare[r] => rmState[r] # "working"
    /\ \A r \in RMs: (oncePrepare[r] /\ rmState[r] = "abort") => onceAbort[r]
    \* /\ TypeOK \* Ok it's fine to just uset TypeOK.
\* ToyR is ok to assume, because the other side of the rule application guarantees ToyR


=============================================================================
\* Modification History
\* Last modified Mon Jun 09 18:34:44 EDT 2025 by johnnguyen
\* Created Fri Jun 06 14:22:31 EDT 2025 by johnnguyen

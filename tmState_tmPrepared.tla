------------------------- MODULE tmState_tmPrepared -------------------------
CONSTANT RMs

VARIABLES tmState, tmPrepared

vars == <<tmState, tmPrepared>>

Init ==
    /\ tmState = "init"
    /\ tmPrepared = {}
    
\* No SndPrepare

RcvPrepare(rm) ==
    /\ tmState = "init"
    /\ tmPrepared' = tmPrepared \cup {rm}
    /\ UNCHANGED(tmState)
    
SndCommit(rm) ==
    /\ tmState \in {"init", "committed"}
    /\ tmState' = "committed"
    /\ tmPrepared = RMs
    /\ UNCHANGED(tmPrepared)

\* No RcvCommit

SndAbort(rm) ==
    /\ tmState \in {"init", "aborted"}
    /\ tmState' = "aborted"
    /\ UNCHANGED(tmPrepared)
    
\* No RcvAbort

\* No SilentAbort

Next == 
    \E rm \in RMs:
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ SndAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ tmState \in {"init", "committed", "aborted"}
    /\ tmPrepared \in SUBSET RMs

=============================================================================
\* Modification History
\* Last modified Thu Jun 19 04:22:36 EDT 2025 by johnnguyen
\* Created Thu Jun 19 04:11:38 EDT 2025 by johnnguyen

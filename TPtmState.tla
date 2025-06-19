----------------------------- MODULE TPtmState -----------------------------
CONSTANT RMs

VARIABLES tmState

vars == <<tmState>>

Init ==
    tmState = "init"
    
\* No SndPrepare

RcvPrepare(rm) ==
    tmState = "init"
    
SndCommit(rm) ==
    /\ tmState \in {"init", "committed"}
    /\ tmState' = "committed"

\* No RcvCommit

SndAbort(rm) ==
    /\ tmState \in {"init", "aborted"}
    /\ tmState' = "aborted"
    
\* No RcvAbort

\* No SilentAbort

Next == 
    \E rm \in RMs:
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ SndAbort(rm)

Spec == Init /\ [][Next]_vars

TypeOK ==
    tmState \in {"init", "committed", "aborted"}

=============================================================================
\* Modification History
\* Last modified Sat Jun 14 15:32:05 EDT 2025 by johnnguyen
\* Created Sat Jun 14 15:16:54 EDT 2025 by johnnguyen

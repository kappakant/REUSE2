---------------------------- MODULE tmPrepared ----------------------------
CONSTANT RMs

VARIABLES tmPrepared

vars == <<tmPrepared>>

Init ==
    tmPrepared = {}
    
\* No SndPrepare

RcvPrepare(rm) ==
    tmPrepared' = tmPrepared \cup {rm}
    
SndCommit(rm) ==
    /\ tmPrepared = RMs
    /\ UNCHANGED(tmPrepared)

\* No RcvCommit

\* No SndAbort

\* No RcvAbort

\* No SilentAbort

Next == 
    \E rm \in RMs:
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        
Spec == Init /\ [][Next]_vars

TypeOK ==
    tmPrepared \in SUBSET RMs

=============================================================================
\* Modification History
\* Last modified Wed Jun 18 17:22:06 EDT 2025 by johnnguyen
\* Created Sat Jun 14 15:24:15 EDT 2025 by johnnguyen

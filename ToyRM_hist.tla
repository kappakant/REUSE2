--------------------------- MODULE ToyRM_hist ---------------------------


CONSTANTS RMs

VARIABLES rmState

vars == <<rmState>>

CandSep ==
TRUE

Init ==
/\ rmState = [rm \in RMs |-> "working"]

Prepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED<<>>
/\ CandSep'

Commit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "commit"]
/\ UNCHANGED<<>>
/\ CandSep'

Abort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ UNCHANGED<<>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ UNCHANGED<<>>
/\ CandSep'

Next ==
\E r \in RMs :
\/ Prepare(r)
\/ Commit(r)
\/ Abort(r)
\/ SilentAbort(r)

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "abort" /\ rmState[rm2] = "commit")))

Spec == (Init /\ [][Next]_vars)
=============================================================================

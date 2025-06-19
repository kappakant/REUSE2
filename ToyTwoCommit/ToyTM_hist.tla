--------------------------- MODULE ToyTM_hist ---------------------------


CONSTANTS RMs

VARIABLES tmState, tmPrepared

vars == <<tmState, tmPrepared>>

CandSep ==
/\ /\ UNSAT

Init ==
/\ tmState = "init"
/\ tmPrepared = {}

Prepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED tmState
/\ UNCHANGED<<>>

Commit(rm) ==
/\ (tmState \in {"init","commit"})
/\ tmPrepared = RMs
/\ tmState' = "commit"
/\ UNCHANGED tmPrepared
/\ UNCHANGED<<>>

Abort(rm) ==
/\ (tmState \in {"init","abort"})
/\ tmState' = "abort"
/\ UNCHANGED tmPrepared
/\ UNCHANGED<<>>

Next ==
\E r \in RMs :
\/ Prepare(r)
\/ Commit(r)
\/ Abort(r)

Spec == (Init /\ [][Next]_vars)
=============================================================================

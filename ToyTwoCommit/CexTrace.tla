--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS res1, res3, res2, RMs

VARIABLES tmState, err, tmPrepared, cexTraceIdx

vars == <<tmState, err, tmPrepared, cexTraceIdx>>

NoErr == err = FALSE

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ cexTraceIdx = 0
/\ err = FALSE

Prepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED tmState
/\ cexTraceIdx' = cexTraceIdx + 1

Commit(rm) ==
/\ (tmState \in {"init","commit"})
/\ tmPrepared = RMs
/\ tmState' = "commit"
/\ UNCHANGED tmPrepared
/\ cexTraceIdx' = cexTraceIdx + 1

Abort(rm) ==
/\ (tmState \in {"init","abort"})
/\ tmState' = "abort"
/\ UNCHANGED tmPrepared
/\ cexTraceIdx' = cexTraceIdx + 1

Next ==
\E r \in RMs :
\/ Prepare(r)
\/ Commit(r)
\/ Abort(r)

Spec == (Init /\ [][Next]_vars)

TraceConstraint ==
/\ cexTraceIdx = 0 => Prepare(res1) /\ err' = err
/\ cexTraceIdx = 1 => Abort(res1) /\ err' = err
/\ cexTraceIdx = 2 => Commit(res2) /\ err' = TRUE
/\ cexTraceIdx >= 3 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================

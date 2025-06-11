--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS res1, res3, res2, RMs

VARIABLES Fluent3_0, err, rmState, Fluent2_0, cexTraceIdx

vars == <<Fluent3_0, err, rmState, Fluent2_0, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in RMs : (Fluent2_0[var0] => Fluent3_0[var0]))

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ Fluent3_0 = [x0 \in RMs |-> FALSE]
/\ Fluent2_0 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ err = FALSE

Prepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ Fluent3_0' = [Fluent3_0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent2_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Commit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "commit"]
/\ Fluent2_0' = [Fluent2_0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent3_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Abort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ UNCHANGED <<Fluent3_0,Fluent2_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ UNCHANGED <<Fluent3_0,Fluent2_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

Next ==
\E r \in RMs :
\/ Prepare(r)
\/ Commit(r)
\/ Abort(r)
\/ SilentAbort(r)

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "abort" /\ rmState[rm2] = "commit")))

Spec == (Init /\ [][Next]_vars)

TraceConstraint ==
/\ cexTraceIdx = 0 => Prepare(res1) /\ err' = err
/\ cexTraceIdx = 1 => Prepare(res2) /\ err' = err
/\ cexTraceIdx = 2 => Prepare(res3) /\ err' = err
/\ cexTraceIdx = 3 => Commit(res1) /\ err' = err
/\ cexTraceIdx = 4 => Commit(res2) /\ err' = err
/\ cexTraceIdx = 5 => Abort(res2) /\ err' = TRUE
/\ cexTraceIdx >= 6 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================

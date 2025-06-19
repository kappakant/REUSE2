--------------------------- MODULE ToyRM_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent6_0, Fluent14_0, Fluent7_0, rmState, Fluent13_0

vars == <<Fluent6_0, Fluent14_0, Fluent7_0, rmState, Fluent13_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent14_0[var0]) => (~(Fluent13_0[var0]))
/\ \A var0 \in RMs : (Fluent6_0[var0]) => (Fluent7_0[var0])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent14_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

Prepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = FALSE]
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![rm] = FALSE]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent14_0>>
/\ CandSep'

Commit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "commit"]
/\ Fluent6_0' = [x0 \in RMs |-> TRUE]
/\ Fluent13_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent14_0, Fluent7_0>>
/\ CandSep'

Abort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ Fluent14_0' = [Fluent14_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent13_0, Fluent7_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ UNCHANGED<<Fluent6_0, Fluent14_0, Fluent13_0, Fluent7_0>>
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

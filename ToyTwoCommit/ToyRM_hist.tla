--------------------------- MODULE ToyRM_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent15_0, Fluent6_0, Fluent14_0, Fluent17_0, Fluent18_0, Fluent7_0, rmState

vars == <<Fluent15_0, Fluent6_0, Fluent14_0, Fluent17_0, Fluent18_0, Fluent7_0, rmState>>

CandSep ==
/\ \A var0 \in RMs : (Fluent14_0[var0]) => (~(Fluent15_0[var0]))
/\ \A var0 \in RMs : (Fluent6_0[var0]) => (Fluent7_0[var0])
/\ \A var0 \in RMs : (Fluent17_0[var0]) => (~(Fluent18_0[var0]))

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ Fluent15_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent14_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent17_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent18_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

Prepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent15_0, Fluent6_0, Fluent14_0, Fluent17_0, Fluent18_0>>
/\ CandSep'

Commit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "commit"]
/\ Fluent15_0' = [[x0 \in RMs |-> TRUE] EXCEPT ![rm] = FALSE]
/\ Fluent6_0' = [[x0 \in RMs |-> TRUE] EXCEPT ![rm] = FALSE]
/\ Fluent17_0' = [Fluent17_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent14_0, Fluent18_0, Fluent7_0>>
/\ CandSep'

Abort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ Fluent14_0' = [Fluent14_0 EXCEPT ![rm] = TRUE]
/\ Fluent18_0' = [Fluent18_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent15_0, Fluent6_0, Fluent17_0, Fluent7_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ UNCHANGED<<Fluent15_0, Fluent6_0, Fluent14_0, Fluent17_0, Fluent18_0, Fluent7_0>>
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

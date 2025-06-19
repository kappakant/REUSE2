--------------------------- MODULE ToyTM_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent6_0, Fluent14_0, tmState, tmPrepared, Fluent7_0, Fluent13_0

vars == <<Fluent6_0, Fluent14_0, tmState, tmPrepared, Fluent7_0, Fluent13_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent14_0[var0]) => (~(Fluent13_0[var0]))
/\ \A var0 \in RMs : (Fluent6_0[var0]) => (Fluent7_0[var0])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent14_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

Prepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED tmState
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = FALSE]
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![rm] = FALSE]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent14_0>>

Commit(rm) ==
/\ (tmState \in {"init","commit"})
/\ tmPrepared = RMs
/\ tmState' = "commit"
/\ UNCHANGED tmPrepared
/\ Fluent6_0' = [x0 \in RMs |-> TRUE]
/\ Fluent13_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent14_0, Fluent7_0>>

Abort(rm) ==
/\ (tmState \in {"init","abort"})
/\ tmState' = "abort"
/\ UNCHANGED tmPrepared
/\ Fluent14_0' = [Fluent14_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent13_0, Fluent7_0>>

Next ==
\E r \in RMs :
\/ Prepare(r)
\/ Commit(r)
\/ Abort(r)

Spec == (Init /\ [][Next]_vars)
=============================================================================

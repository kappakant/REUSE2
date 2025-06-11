--------------------------- MODULE ToyTM_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent15_0, Fluent6_0, Fluent14_0, tmState, Fluent17_0, Fluent18_0, tmPrepared, Fluent7_0

vars == <<Fluent15_0, Fluent6_0, Fluent14_0, tmState, Fluent17_0, Fluent18_0, tmPrepared, Fluent7_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent14_0[var0]) => (~(Fluent15_0[var0]))
/\ \A var0 \in RMs : (Fluent6_0[var0]) => (Fluent7_0[var0])
/\ \A var0 \in RMs : (Fluent17_0[var0]) => (~(Fluent18_0[var0]))

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent15_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent14_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent17_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent18_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

Prepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED tmState
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent15_0, Fluent6_0, Fluent14_0, Fluent17_0, Fluent18_0>>

Commit(rm) ==
/\ (tmState \in {"init","commit"})
/\ tmPrepared = RMs
/\ tmState' = "commit"
/\ UNCHANGED tmPrepared
/\ Fluent15_0' = [[x0 \in RMs |-> TRUE] EXCEPT ![rm] = FALSE]
/\ Fluent6_0' = [[x0 \in RMs |-> TRUE] EXCEPT ![rm] = FALSE]
/\ Fluent17_0' = [Fluent17_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent14_0, Fluent18_0, Fluent7_0>>

Abort(rm) ==
/\ (tmState \in {"init","abort"})
/\ tmState' = "abort"
/\ UNCHANGED tmPrepared
/\ Fluent14_0' = [Fluent14_0 EXCEPT ![rm] = TRUE]
/\ Fluent18_0' = [Fluent18_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent15_0, Fluent6_0, Fluent17_0, Fluent7_0>>

Next ==
\E r \in RMs :
\/ Prepare(r)
\/ Commit(r)
\/ Abort(r)

Spec == (Init /\ [][Next]_vars)
=============================================================================

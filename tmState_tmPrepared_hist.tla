--------------------------- MODULE tmState_tmPrepared_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent6_0, tmState, Fluent19_0, Fluent18_0, Fluent9_0, tmPrepared, Fluent7_0, Fluent10_0, Fluent13_0, Fluent12_0

vars == <<Fluent6_0, tmState, Fluent19_0, Fluent18_0, Fluent9_0, tmPrepared, Fluent7_0, Fluent10_0, Fluent13_0, Fluent12_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent12_0[var0]) => (~(Fluent13_0[var0]))
/\ \A var0 \in RMs : (Fluent19_0[var0]) => (Fluent18_0[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent6_0[var1]) => (Fluent7_0[var0])
/\ \A var0 \in RMs : (Fluent10_0[var0]) => (Fluent9_0[var0])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent19_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent18_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent9_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED tmState
/\ Fluent18_0' = [Fluent18_0 EXCEPT ![rm] = TRUE]
/\ Fluent9_0' = [[x0 \in RMs |-> FALSE] EXCEPT ![rm] = TRUE]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent19_0, Fluent10_0, Fluent13_0>>

SndCommit(rm) ==
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ tmPrepared = RMs
/\ UNCHANGED tmPrepared
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ Fluent19_0' = [Fluent19_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent18_0, Fluent9_0, Fluent7_0, Fluent10_0, Fluent13_0, Fluent12_0>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED tmPrepared
/\ Fluent18_0' = [x0 \in RMs |-> FALSE]
/\ Fluent9_0' = [Fluent9_0 EXCEPT ![rm] = TRUE]
/\ Fluent10_0' = [Fluent10_0 EXCEPT ![rm] = TRUE]
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![rm] = TRUE]
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent6_0, Fluent19_0, Fluent7_0>>

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
=============================================================================

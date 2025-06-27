--------------------------- MODULE tmState_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent14_0, tmState, Fluent13_0

vars == <<Fluent14_0, tmState, Fluent13_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent13_0[var1]) => (~(Fluent14_0[var0]))

Init ==
/\ tmState = "init"
/\ Fluent14_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ UNCHANGED tmState
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>

SndCommit(rm) ==
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent14_0>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ Fluent14_0' = [Fluent14_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent13_0>>

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK == (tmState \in {"init","committed","aborted"})
=============================================================================

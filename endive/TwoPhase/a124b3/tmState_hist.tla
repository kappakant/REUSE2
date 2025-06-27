--------------------------- MODULE tmState_hist ---------------------------
EXTENDS Randomization

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

NextUnchanged == UNCHANGED vars

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK == (tmState \in {"init","committed","aborted"})

NumRandElems == 5
TypeOKRand ==
/\ (tmState \in RandomSubset(NumRandElems, {"init", "committed", "aborted"}))
/\ Fluent14_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent13_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

\* Added by endive
Inv46_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "aborted") \/ (~(Fluent14_0[rmi]))
Inv51_1_1_def == \A rmi \in RMs : \A rmj \in RMs : (tmState = "committed") \/ (~(Fluent13_0[rmi]))

\* The inductive invariant candidate.
IndAuto ==
/\ CandSep
/\ Inv46_1_0_def
/\ Inv51_1_1_def

=============================================================================

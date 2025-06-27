--------------------------- MODULE tmPrepared_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

VARIABLES Fluent6_0, tmPrepared, Fluent7_0

vars == <<Fluent6_0, tmPrepared, Fluent7_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var0]) => (Fluent6_0[var1])

Init ==
/\ tmPrepared = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent7_0>>

SndCommit(rm) ==
/\ tmPrepared = RMs
/\ UNCHANGED tmPrepared
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0>>

NextUnchanged == UNCHANGED vars

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK == (tmPrepared \in SUBSET(RMs))

NumRandElems == 5
TypeOKRand ==
/\ (tmPrepared \in RandomSubset(NumRandElems, SUBSET(RMs)))
/\ Fluent6_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent7_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

=============================================================================

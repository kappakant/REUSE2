--------------------------- MODULE rmState_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

\* Manually pruned (11)
VARIABLES Fluent6_0, Fluent7_0, rmState, Fluent10_0

vars == <<Fluent6_0, Fluent7_0, rmState, Fluent10_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent6_0[var0]) => (Fluent10_0[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var1]) => (~(Fluent6_0[var0]))

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ Fluent10_0' = [Fluent10_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent7_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent10_0, Fluent7_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent10_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED<<Fluent6_0, Fluent10_0, Fluent7_0>>
/\ CandSep'

NextUnchanged == UNCHANGED vars

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvCommit(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ Fluent6_0  \in [RMs -> BOOLEAN]
/\ Fluent7_0 \in [RMs -> BOOLEAN]
/\ Fluent10_0  \in [RMs -> BOOLEAN]

NumRandElems == 5
TypeOKRand ==
/\ (rmState \in RandomSubset(NumRandElems, [RMs -> {"working","prepared","committed","aborted"}]))
/\ Fluent6_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent7_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent10_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

\* added by endive
Inv68_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent6_0[rmi]) \/ (~(rmState[rmi] = "committed"))
Inv169_1_1_def == \A rmi \in RMs : \A rmj \in RMs : (rmState[rmi] = "committed") \/ (~(Fluent6_0[rmi]))
Inv281_1_2_def == \A rmi \in RMs : \A rmj \in RMs : ~(Fluent10_0[rmi]) \/ (~(rmState[rmi] = "working"))
Inv1252_2_3_def == \A rmi \in RMs : \A rmj \in RMs : (Fluent7_0[rmi]) \/ (~(rmState[rmi] = "aborted")) \/ (~(Fluent10_0[rmi]))

\* The inductive invariant candidate.
IndAuto ==
/\ Consistent
/\ Inv68_1_0_def
/\ Inv169_1_1_def
/\ Inv281_1_2_def
/\ Inv1252_2_3_def
=============================================================================

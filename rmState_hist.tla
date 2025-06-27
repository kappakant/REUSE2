--------------------------- MODULE rmState_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent6_0, Fluent7_0, rmState, Fluent11_0, Fluent10_0

vars == <<Fluent6_0, Fluent7_0, rmState, Fluent11_0, Fluent10_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent11_0[var0]) => (Fluent10_0[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var1]) => (~(Fluent6_0[var0]))

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent11_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ Fluent10_0' = [Fluent10_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent11_0, Fluent7_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ Fluent11_0' = [Fluent11_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent10_0, Fluent7_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent11_0, Fluent10_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED<<Fluent6_0, Fluent11_0, Fluent10_0, Fluent7_0>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvCommit(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================

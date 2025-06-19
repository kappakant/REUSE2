--------------------------- MODULE rmState_tmPrepared_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent6_0, Fluent5_0, Fluent4_0, Fluent17_0, Fluent3_0, Fluent18_0, tmPrepared, rmState

vars == <<Fluent6_0, Fluent5_0, Fluent4_0, Fluent17_0, Fluent3_0, Fluent18_0, tmPrepared, rmState>>

CandSep ==
/\ \A var0 \in RMs : \E var1 \in RMs : (Fluent4_0[var0]) => (Fluent3_0[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent18_0[var0]) => (~(Fluent17_0[var1]))
/\ \A var0 \in RMs : (Fluent6_0[var0]) => (Fluent5_0[var0])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ tmPrepared = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent4_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent17_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent3_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent18_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED tmPrepared
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent4_0, Fluent17_0, Fluent3_0, Fluent18_0>>
/\ CandSep'

SndCommit(rm) ==
/\ tmPrepared = RMs
/\ UNCHANGED rmState
/\ UNCHANGED tmPrepared
/\ Fluent3_0' = [Fluent3_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent17_0, Fluent18_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED rmState
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent4_0, Fluent17_0, Fluent3_0, Fluent18_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED tmPrepared
/\ Fluent4_0' = [Fluent4_0 EXCEPT ![rm] = TRUE]
/\ Fluent18_0' = [Fluent18_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent17_0, Fluent3_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED tmPrepared
/\ Fluent17_0' = [Fluent17_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent3_0, Fluent18_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED tmPrepared
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent4_0, Fluent17_0, Fluent3_0, Fluent18_0>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ SndCommit(rm)
\/ RcvPrepare(rm)
\/ RcvCommit(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmPrepared \in SUBSET(RMs))

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================

--------------------------- MODULE rmState_msgs_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent6_0, msgs, Fluent19_0, Fluent18_0, Fluent9_0, Fluent7_0, rmState, Fluent10_0, Fluent13_0, Fluent12_0

vars == <<Fluent6_0, msgs, Fluent19_0, Fluent18_0, Fluent9_0, Fluent7_0, rmState, Fluent10_0, Fluent13_0, Fluent12_0>>

CandSep ==
/\ \A var0 \in RMs : (Fluent12_0[var0]) => (~(Fluent13_0[var0]))
/\ \A var0 \in RMs : (Fluent19_0[var0]) => (Fluent18_0[var0])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent6_0[var1]) => (Fluent7_0[var0])
/\ \A var0 \in RMs : (Fluent10_0[var0]) => (Fluent9_0[var0])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ msgs = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent19_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent18_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent9_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED<<Fluent6_0, Fluent19_0, Fluent18_0, Fluent9_0, Fluent7_0, Fluent10_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED rmState
/\ Fluent18_0' = [Fluent18_0 EXCEPT ![rm] = TRUE]
/\ Fluent9_0' = [[x0 \in RMs |-> FALSE] EXCEPT ![rm] = TRUE]
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent19_0, Fluent10_0, Fluent13_0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ UNCHANGED rmState
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ Fluent19_0' = [Fluent19_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent18_0, Fluent9_0, Fluent7_0, Fluent10_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED<<Fluent6_0, Fluent19_0, Fluent18_0, Fluent9_0, Fluent7_0, Fluent10_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED rmState
/\ Fluent18_0' = [x0 \in RMs |-> FALSE]
/\ Fluent9_0' = [Fluent9_0 EXCEPT ![rm] = TRUE]
/\ Fluent10_0' = [Fluent10_0 EXCEPT ![rm] = TRUE]
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![rm] = TRUE]
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = FALSE]
/\ UNCHANGED<<Fluent6_0, Fluent19_0, Fluent7_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED<<Fluent6_0, Fluent19_0, Fluent18_0, Fluent9_0, Fluent7_0, Fluent10_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED msgs
/\ UNCHANGED<<Fluent6_0, Fluent19_0, Fluent18_0, Fluent9_0, Fluent7_0, Fluent10_0, Fluent13_0, Fluent12_0>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ RcvAbort(rm)
\/ SndAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (msgs \in SUBSET(Message))

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================

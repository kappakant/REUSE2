--------------------------- MODULE rmState_msgs_tmPrepared_hist ---------------------------


CONSTANTS RMs

VARIABLES msgs, Fluent14_0, tmPrepared, rmState, Fluent13_0

vars == <<msgs, Fluent14_0, tmPrepared, rmState, Fluent13_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent13_0[var1]) => (~(Fluent14_0[var0]))

Init ==
/\ tmPrepared = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ msgs = {}
/\ Fluent14_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED msgs
/\ UNCHANGED rmState
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmPrepared = RMs
/\ UNCHANGED <<rmState,tmPrepared>>
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent14_0>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmPrepared
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<rmState,tmPrepared>>
/\ Fluent14_0' = [Fluent14_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent13_0>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmPrepared
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED msgs
/\ UNCHANGED tmPrepared
/\ UNCHANGED<<Fluent14_0, Fluent13_0>>
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
/\ (tmPrepared \in SUBSET(RMs))

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================

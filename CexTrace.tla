--------------------------- MODULE CexTrace ---------------------------
EXTENDS Naturals, TLC

CONSTANTS res1, res3, res2, RMs

VARIABLES Fluent6_0, msgs, Fluent5_0, err, tmPrepared, rmState, cexTraceIdx

vars == <<Fluent6_0, msgs, Fluent5_0, err, tmPrepared, rmState, cexTraceIdx>>

NoErr == err = FALSE

CandSep == (\A var0 \in RMs : (Fluent6_0[var0] => ~(Fluent5_0[var0])))

Init ==
/\ tmPrepared = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ msgs = {}
/\ Fluent6_0 = [x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [x0 \in RMs |-> FALSE]
/\ cexTraceIdx = 0
/\ err = FALSE

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED <<Fluent6_0,Fluent5_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED msgs
/\ UNCHANGED rmState
/\ UNCHANGED <<Fluent6_0,Fluent5_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ tmPrepared = RMs
/\ UNCHANGED <<rmState,tmPrepared>>
/\ Fluent5_0' = [Fluent5_0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent6_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmPrepared
/\ UNCHANGED <<Fluent6_0,Fluent5_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<rmState,tmPrepared>>
/\ Fluent6_0' = [Fluent6_0 EXCEPT![rm] = TRUE]
/\ UNCHANGED <<Fluent5_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED msgs
/\ UNCHANGED tmPrepared
/\ UNCHANGED <<Fluent6_0,Fluent5_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED msgs
/\ UNCHANGED tmPrepared
/\ UNCHANGED <<Fluent6_0,Fluent5_0>>
/\ CandSep'
/\ cexTraceIdx' = cexTraceIdx + 1

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

TraceConstraint ==
/\ cexTraceIdx = 0 => SndPrepare(res1) /\ err' = err
/\ cexTraceIdx = 1 => RcvPrepare(res1) /\ err' = err
/\ cexTraceIdx = 2 => SndPrepare(res2) /\ err' = err
/\ cexTraceIdx = 3 => RcvPrepare(res2) /\ err' = err
/\ cexTraceIdx = 4 => SndPrepare(res3) /\ err' = err
/\ cexTraceIdx = 5 => RcvPrepare(res3) /\ err' = err
/\ cexTraceIdx = 6 => SndAbort(res1) /\ err' = err
/\ cexTraceIdx = 7 => RcvAbort(res1) /\ err' = err
/\ cexTraceIdx = 8 => SndCommit(res2) /\ err' = err
/\ cexTraceIdx = 9 => RcvCommit(res2) /\ err' = TRUE
/\ cexTraceIdx >= 10 => FALSE

InternalAction == UNCHANGED<<cexTraceIdx,err>>

TraceConstraintSpec == Init /\ [][Next /\ (TraceConstraint \/ InternalAction)]_vars
=============================================================================

--------------------------- MODULE msgs_tmState_tmPrepared_hist ---------------------------
EXTENDS Randomization

CONSTANTS RMs

\* Manually pruned (11)
VARIABLES Fluent6_0, msgs, tmState, tmPrepared, Fluent7_0, Fluent10_0

vars == <<Fluent6_0, msgs, tmState, tmPrepared, Fluent7_0, Fluent10_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent6_0[var0]) => (Fluent10_0[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent7_0[var1]) => (~(Fluent6_0[var0]))

Init ==
/\ msgs = {}
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent10_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent7_0 = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED <<tmState,tmPrepared>>
/\ Fluent10_0' = [Fluent10_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent7_0>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState>>
/\ UNCHANGED<<Fluent6_0, Fluent10_0, Fluent7_0>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ tmPrepared = RMs
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<Fluent6_0, Fluent10_0, Fluent7_0>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent10_0, Fluent7_0>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED <<tmPrepared>>
/\ UNCHANGED<<Fluent6_0, Fluent10_0, Fluent7_0>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ Fluent7_0' = [Fluent7_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent10_0>>

NextUnchanged == UNCHANGED vars

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)

Spec == (Init /\ [][Next]_vars)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

TypeOK ==
/\ (msgs \in SUBSET(Message))
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent6_0  \in [RMs -> BOOLEAN]
/\ Fluent7_0 \in [RMs -> BOOLEAN]
/\ Fluent10_0  \in [RMs -> BOOLEAN]


NumRandElems == 5
TypeOKRand ==
/\ (msgs \in RandomSubset(NumRandElems, SUBSET(Message)))
/\ (tmState \in RandomSubset(NumRandElems ,{"init","committed","aborted"}))
/\ (tmPrepared \in RandomSubset(NumRandElems, SUBSET(RMs)))
/\ Fluent6_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent7_0 \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])
/\ Fluent10_0  \in RandomSubset(NumRandElems, [RMs -> BOOLEAN])

=============================================================================


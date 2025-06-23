--------------------------- MODULE tmState_tmPrepared_hist ---------------------------


CONSTANTS RMs

VARIABLES Fluent6_0, Fluent5_0, tmState, Fluent19_0, Fluent9_0, tmPrepared, Fluent8_0, Fluent20_0, Fluent13_0, Fluent12_0

vars == <<Fluent6_0, Fluent5_0, tmState, Fluent19_0, Fluent9_0, tmPrepared, Fluent8_0, Fluent20_0, Fluent13_0, Fluent12_0>>

CandSep ==
/\ \A var0 \in RMs : \A var1 \in RMs : (Fluent6_0[var1]) => (Fluent5_0[var0])
/\ \A var0 \in RMs : (Fluent9_0[var0]) => (~(Fluent8_0[var0]))
/\ \A var0 \in RMs : (Fluent13_0[var0]) => (~(Fluent12_0[var0]))
/\ \A var0 \in RMs : (Fluent20_0[var0]) => (Fluent19_0[var0])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ Fluent6_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent5_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent19_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent9_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent8_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent20_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent13_0 = [ x0 \in RMs |-> FALSE]
/\ Fluent12_0 = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED tmState
/\ Fluent5_0' = [Fluent5_0 EXCEPT ![rm] = TRUE]
/\ Fluent19_0' = [Fluent19_0 EXCEPT ![rm] = TRUE]
/\ Fluent8_0' = [x0 \in RMs |-> TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent9_0, Fluent20_0, Fluent13_0, Fluent12_0>>

SndCommit(rm) ==
/\ (tmState \in {"init","committed"})
/\ tmState' = "committed"
/\ tmPrepared = RMs
/\ UNCHANGED tmPrepared
/\ Fluent6_0' = [Fluent6_0 EXCEPT ![rm] = TRUE]
/\ Fluent20_0' = [Fluent20_0 EXCEPT ![rm] = TRUE]
/\ Fluent13_0' = [Fluent13_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent5_0, Fluent19_0, Fluent9_0, Fluent8_0, Fluent12_0>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED tmPrepared
/\ Fluent19_0' = [[x0 \in RMs |-> FALSE] EXCEPT ![rm] = TRUE]
/\ Fluent9_0' = [Fluent9_0 EXCEPT ![rm] = TRUE]
/\ Fluent8_0' = [Fluent8_0 EXCEPT ![rm] = FALSE]
/\ Fluent12_0' = [Fluent12_0 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<Fluent6_0, Fluent5_0, Fluent20_0, Fluent13_0>>

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ Fluent6_0 =  [RMs -> BOOLEAN]
/\ Fluent5_0 =  [RMs -> BOOLEAN]
/\ Fluent19_0 = [RMs -> BOOLEAN]
/\ Fluent9_0 =  [RMs -> BOOLEAN]
/\ Fluent8_0 =  [RMs -> BOOLEAN]
/\ Fluent20_0 = [RMs -> BOOLEAN]
/\ Fluent13_0 = [RMs -> BOOLEAN]
/\ Fluent12_0 = [RMs -> BOOLEAN]


=============================================================================

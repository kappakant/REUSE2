--------------------------- MODULE ToyTMCarini ---------------------------


CONSTANTS RMs

VARIABLES lastCommit15, lastCommit6, onceAbort14, tmState, onceCommit17, onceAbort18, tmPrepared, oncePrepare7

vars == <<lastCommit15, lastCommit6, onceAbort14, tmState, onceCommit17, onceAbort18, tmPrepared, oncePrepare7>>

CandSep ==
/\ \A var0 \in RMs : (onceAbort14[var0]) => (~(lastCommit15[var0]))
/\ \A var0 \in RMs : (lastCommit6[var0]) => (oncePrepare7[var0])
/\ \A var0 \in RMs : (onceCommit17[var0]) => (~(onceAbort18[var0]))

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ lastCommit15 = [ x0 \in RMs |-> FALSE]
/\ lastCommit6 = [ x0 \in RMs |-> FALSE]
/\ onceAbort14 = [ x0 \in RMs |-> FALSE]
/\ onceCommit17 = [ x0 \in RMs |-> FALSE]
/\ onceAbort18 = [ x0 \in RMs |-> FALSE]
/\ oncePrepare7 = [ x0 \in RMs |-> FALSE]

Prepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED tmState
/\ oncePrepare7' = [oncePrepare7 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<lastCommit15, lastCommit6, onceAbort14, onceCommit17, onceAbort18>>

Commit(rm) ==
/\ (tmState \in {"init","commit"})
/\ tmPrepared = RMs
/\ tmState' = "commit"
/\ UNCHANGED tmPrepared
/\ lastCommit15' = [[x0 \in RMs |-> TRUE] EXCEPT ![rm] = FALSE]
/\ lastCommit6' = [[x0 \in RMs |-> TRUE] EXCEPT ![rm] = FALSE]
/\ onceCommit17' = [onceCommit17 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<onceAbort14, onceAbort18, oncePrepare7>>

Abort(rm) ==
/\ (tmState \in {"init","abort"})
/\ tmState' = "abort"
/\ UNCHANGED tmPrepared
/\ onceAbort14' = [onceAbort14 EXCEPT ![rm] = TRUE]
/\ onceAbort18' = [onceAbort18 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<lastCommit15, lastCommit6, onceCommit17, oncePrepare7>>

Next ==
\E r \in RMs :
\/ Prepare(r)
\/ Commit(r)
\/ Abort(r)

Spec == (Init /\ [][Next]_vars)
=============================================================================

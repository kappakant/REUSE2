--------------------------- MODULE ToyRMCarini ---------------------------


CONSTANTS RMs

VARIABLES lastCommit15, lastCommit6, onceAbort14, onceCommit17, onceAbort18, oncePrepare7, rmState

vars == <<lastCommit15, lastCommit6, onceAbort14, onceCommit17, onceAbort18, oncePrepare7, rmState>>

CandSep ==
/\ \A var0 \in RMs : (onceAbort14[var0]) => (~(lastCommit15[var0]))
/\ \A var0 \in RMs : (lastCommit6[var0]) => (oncePrepare7[var0])
/\ \A var0 \in RMs : (onceCommit17[var0]) => (~(onceAbort18[var0]))

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ lastCommit15 = [ x0 \in RMs |-> FALSE]
/\ lastCommit6 = [ x0 \in RMs |-> FALSE]
/\ onceAbort14 = [ x0 \in RMs |-> FALSE]
/\ onceCommit17 = [ x0 \in RMs |-> FALSE]
/\ onceAbort18 = [ x0 \in RMs |-> FALSE]
/\ oncePrepare7 = [ x0 \in RMs |-> FALSE]

\* All of them force CandSep to be invariant, presumably because ToyTM guarantees that for us.
Prepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ oncePrepare7' = [oncePrepare7 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<lastCommit15, lastCommit6, onceAbort14, onceCommit17, onceAbort18>>
/\ CandSep'

Commit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "commit"]
/\ lastCommit15' = [[x0 \in RMs |-> TRUE] EXCEPT ![rm] = FALSE]
/\ lastCommit6' = [[x0 \in RMs |-> TRUE] EXCEPT ![rm] = FALSE]
/\ onceCommit17' = [onceCommit17 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<onceAbort14, onceAbort18, oncePrepare7>>
/\ CandSep'

Abort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ onceAbort14' = [onceAbort14 EXCEPT ![rm] = TRUE]
/\ onceAbort18' = [onceAbort18 EXCEPT ![rm] = TRUE]
/\ UNCHANGED<<lastCommit15, lastCommit6, onceCommit17, oncePrepare7>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "abort"]
/\ UNCHANGED<<lastCommit15, lastCommit6, onceAbort14, onceCommit17, onceAbort18, oncePrepare7>>
/\ CandSep'

Next ==
\E r \in RMs :
\/ Prepare(r)
\/ Commit(r)
\/ Abort(r)
\/ SilentAbort(r)

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "abort" /\ rmState[rm2] = "commit")))

Spec == (Init /\ [][Next]_vars)
=============================================================================

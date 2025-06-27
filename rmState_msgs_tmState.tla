------------------------- MODULE rmState_msgs_tmState -------------------------
CONSTANT RMs

VARIABLES rmState, msgs, tmState

vars == <<rmState, msgs, tmState>>

Init ==
    /\ tmState = "init"
    /\ rmState = [rm \in RMs |-> "working"]
    /\ msgs = {}

SndPrepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
    /\ UNCHANGED<<tmState>>

RcvPrepare(rm) ==
    /\ [type |-> "Prepared", theRM |-> rm] \in msgs
    /\ tmState = "init"
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(rmState)
    /\ UNCHANGED(tmState)

SndCommit(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ tmState \in {"init", "committed"}
    /\ tmState' = "committed"
    /\ UNCHANGED(rmState)

RcvCommit(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
    /\ [type |-> "Commit"] \in msgs
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(tmState)

SndAbort(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED(rmState)
    /\ tmState \in {"init", "aborted"}
    /\ tmState' = "aborted"
        
RcvAbort(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ [type |-> "Abort"] \in msgs
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(tmState)
    
SilentAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(tmState)

Next ==
    \E rm \in RMs:
        \/ SndPrepare(rm)
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ RcvCommit(rm)
        \/ RcvAbort(rm)
        \/ SndAbort(rm)
        \/ SilentAbort(rm)
        
Spec == Init /\ [][Next]_vars

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]

TypeOK ==
    /\ rmState \in [RMs -> {"working", "prepared", "committed", "aborted"}]
    /\ msgs \in SUBSET Message
    /\ tmState \in {"init", "committed", "aborted"}
    
Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")
=============================================================================

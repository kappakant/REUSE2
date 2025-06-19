------------------------- MODULE rmState_msgs -------------------------
CONSTANT RMs

VARIABLES rmState, msgs

vars == <<rmState, msgs>>

Init ==
    /\ rmState = [rm \in RMs |-> "working"]
    /\ msgs = {}

SndPrepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}

RcvPrepare(rm) ==
    /\ [type |-> "Prepared", theRM |-> rm] \in msgs
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(rmState)
        
SndCommit(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ UNCHANGED(rmState)

RcvCommit(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
    /\ [type |-> "Commit"] \in msgs
    /\ UNCHANGED(msgs)

SndAbort(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED(rmState)
        
RcvAbort(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ [type |-> "Abort"] \in msgs
    /\ UNCHANGED(msgs)

    
SilentAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED(msgs)
    
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
    
Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")
=============================================================================

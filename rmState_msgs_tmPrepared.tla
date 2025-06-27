------------------------- MODULE rmState_msgs_tmPrepared -------------------------
CONSTANT RMs

VARIABLES rmState, msgs, tmPrepared 

vars == <<rmState, msgs, tmPrepared>>

Init ==
    /\ tmPrepared = {}
    /\ rmState = [rm \in RMs |-> "working"]
    /\ msgs = {}

SndPrepare(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
    /\ UNCHANGED<<tmPrepared>>

RcvPrepare(rm) ==
    /\ [type |-> "Prepared", theRM |-> rm] \in msgs
    /\ tmPrepared' = tmPrepared \cup {rm}
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(rmState)

SndCommit(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ tmPrepared = RMs
    /\ UNCHANGED<<rmState, tmPrepared>>

RcvCommit(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
    /\ [type |-> "Commit"] \in msgs
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(tmPrepared)

SndAbort(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED<<rmState, tmPrepared>>
        
RcvAbort(rm) ==
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ [type |-> "Abort"] \in msgs
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(tmPrepared)
    
SilentAbort(rm) ==
    /\ rmState[rm] = "working"
    /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(tmPrepared)

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
    /\ tmPrepared \in SUBSET RMs
    
Consistent == \A rm1,rm2 \in RMs : ~(rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")
=============================================================================

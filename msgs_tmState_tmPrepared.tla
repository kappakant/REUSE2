------------------------- MODULE msgs_tmState_tmPrepared -------------------------
CONSTANT RMs

VARIABLES msgs, tmState, tmPrepared

vars == <<msgs, tmState, tmPrepared>>

Init ==
    /\ msgs = {}
    /\ tmState = "init"
    /\ tmPrepared = {}

SndPrepare(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
    /\ UNCHANGED<<tmState, tmPrepared>>

RcvPrepare(rm) ==
    /\ [type |-> "Prepared", theRM |-> rm] \in msgs
    /\ tmState = "init"
    /\ tmPrepared' = tmPrepared \cup {rm}
    /\ UNCHANGED<<msgs, tmState>>

SndCommit(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ tmState \in {"init", "committed"}
    /\ tmState' = "committed"
    /\ tmPrepared = RMs
    /\ UNCHANGED<<tmPrepared>>

RcvCommit(rm) ==
    /\ [type |-> "Commit"] \in msgs
    /\ UNCHANGED<<msgs, tmState, tmPrepared>>

SndAbort(rm) ==
    /\ tmState \in {"init", "aborted"}
    /\ tmState' = "aborted"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED<<tmPrepared>>
        
RcvAbort(rm) ==
    /\ [type |-> "Abort"] \in msgs
    /\ UNCHANGED<<msgs, tmState, tmPrepared>>

Next == 
    \E rm \in RMs:
        \/ SndPrepare(rm)
        \/ RcvPrepare(rm)
        \/ SndCommit(rm)
        \/ RcvCommit(rm)
        \/ SndAbort(rm)
        \/ RcvAbort(rm)

Spec == Init /\ [][Next]_vars

Message ==
  [type : {"Prepared"}, theRM : RMs]  \cup  [type : {"Commit", "Abort"}]

TypeOK ==
    /\ msgs \in SUBSET Message
    /\ tmState \in {"init", "committed", "aborted"}
    /\ tmPrepared \in SUBSET RMs

=============================================================================

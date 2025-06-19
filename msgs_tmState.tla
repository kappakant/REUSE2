---------------------------- MODULE msgs_tmState ----------------------------
CONSTANT RMs

VARIABLES msgs, tmState

vars == <<msgs, tmState>>

Init ==
    /\ msgs = {}
    /\ tmState = "init"

SndPrepare(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
    /\ UNCHANGED(tmState)
    
RcvPrepare(rm) ==
    /\ [type |-> "Prepared", theRM |-> rm] \in msgs
    /\ tmState = "init"
    /\ UNCHANGED(tmState)
    /\ UNCHANGED(msgs)
    
SndCommit(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ tmState \in {"init", "committed"}
    /\ tmState' = "committed"

RcvCommit(rm) ==
    /\ [type |-> "Commit"] \in msgs
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(tmState)

SndAbort(rm) ==
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ tmState \in {"init", "aborted"}
    /\ tmState' = "aborted"
    
RcvAbort(rm) ==
    /\ [type |-> "Abort"] \in msgs
    /\ UNCHANGED(msgs)
    /\ UNCHANGED(tmState)

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
=============================================================================
\* Modification History
\* Last modified Thu Jun 19 13:10:04 EDT 2025 by johnnguyen
\* Created Wed Jun 18 17:24:13 EDT 2025 by johnnguyen

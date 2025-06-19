------------------------------- MODULE TPmsgs -------------------------------
CONSTANT RMs

VARIABLES msgs

vars == <<msgs>>

Init ==
    msgs = {}
    
SndPrepare(rm) ==
    msgs' = msgs \cup {[type |-> "Prepared", theRM |-> rm]}
    
RcvPrepare(rm) ==
    [type |-> "Prepared", theRM |-> rm] \in msgs
    
SndCommit(rm) ==
    msgs' = msgs \cup {[type |-> "Commit"]}
  
RcvCommit(rm) ==
    /\ [type |-> "Commit"] \in msgs
    /\ UNCHANGED(msgs)
  
SndAbort(rm) ==
    msgs' = msgs \cup {[type |-> "Abort"]}
  
RcvAbort(rm) ==
    /\ [type |-> "Abort"] \in msgs
    /\ UNCHANGED(msgs)
  
\* No silent abort
\* incomplete      
=============================================================================
\* Modification History
\* Last modified Wed Jun 18 17:50:45 EDT 2025 by johnnguyen
\* Created Sat Jun 14 15:34:01 EDT 2025 by johnnguyen

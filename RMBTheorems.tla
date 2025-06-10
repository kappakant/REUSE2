---------------------------- MODULE RMBTheorems ----------------------------
EXTENDS RMB, RMBLemmas

THEOREM IrmInitialization ==
    Init /\ ToyR => Irm
    <1> SUFFICES ASSUME Init /\ ToyR
                 PROVE Irm
                 OBVIOUS 
           
    <1> SUFFICES ASSUME NEW rm \in RMs, NEW rm2 \in RMs
                 PROVE /\ ~(rmState[rm] = "abort" /\ rmState[rm2] = "commit")
                       /\ onceCommit[rm] <=> rmState[rm] = "commit"
                       /\ oncePrepare[rm] => rmState[rm] # "working"
                       /\ (oncePrepare[rm] /\ rmState[rm] = "abort") => onceAbort[rm]
                 BY DEF Irm, Consistent, TypeOK
    
    <1>a ~(rmState[rm] = "abort" /\ rmState[rm2] = "commit")
        <2>1 rmState[rm] = "working" BY DEF Init, RM!Init
        <2>. QED BY <2>1
                     
                     
    <1>b onceCommit[rm] <=> rmState[rm] = "commit" 
        <2>a onceCommit[rm] = FALSE BY DEF Init, B!Init
        <2>b rmState[rm] = "working" BY DEF Init, RM!Init
        <2>. QED BY <2>a, <2>b
        
        
    <1>c oncePrepare[rm] => rmState[rm] # "working" 
        <2>1 oncePrepare[rm] = FALSE BY DEF Init, B!Init
        <2>. QED BY <2>1
    
    
    <1>d (oncePrepare[rm] /\ rmState[rm] = "abort") => onceAbort[rm]
        <2>1 oncePrepare[rm] = FALSE BY DEF Init, B!Init
        <2>. QED BY <2>1
        
    <1>. QED BY <1>a, <1>b, <1>c, <1>d
    
THEOREM IrmInduction ==
    Irm /\ Next /\ ToyR /\ ToyR' => Irm'
    <1> SUFFICES ASSUME Irm, Next, ToyR, ToyR'
                 PROVE /\ Consistent'
                       /\ \A r \in RMs: onceCommit'[r] <=> rmState'[r] = "commit"
                       /\ \A r \in RMs: oncePrepare'[r] => rmState'[r] # "working"
                       /\ \A r \in RMs: (oncePrepare'[r] /\ rmState'[r] = "abort") => onceAbort'[r]
                 BY DEF Irm
                    
    <1>a Consistent' BY IrmConsistentInduction
    <1>b \A r \in RMs: onceCommit'[r] <=> rmState'[r] = "commit" BY IrmCommitInduction
    <1>c \A r \in RMs: oncePrepare'[r] => rmState'[r] # "working" BY IrmPrepareInduction
    <1>d \A r \in RMs: (oncePrepare'[r] /\ rmState'[r] = "abort") => onceAbort'[r] BY IrmAbortInduction

    <1>. QED BY <1>a, <1>b, <1>c, <1>d
    
THEOREM IrmSafety ==
    Irm => Consistent BY DEF Irm

=============================================================================
\* Modification History
\* Last modified Sun Jun 08 14:19:43 EDT 2025 by johnnguyen
\* Created Fri Jun 06 16:06:40 EDT 2025 by johnnguyen

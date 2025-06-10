---------------------------- MODULE BTMTheorems ----------------------------
EXTENDS BTM, BTMLemmas


THEOREM ItmInitialization ==
    Init => Itm BY DEF Init, B!Init, TM!Init, Itm, TypeOK
    
THEOREM ItmInduction ==
    Itm /\ Next => Itm'
    <1> SUFFICES ASSUME Itm /\ Next, NEW rm \in RMs,
                        SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm)
                 PROVE  /\ TypeOK'
                 
                        /\ \A r \in RMs: r \in tmPrepared' => oncePrepare'[r]
                        /\ tmState' = "commit" => RMs = tmPrepared'
                        
                        /\ (\E r \in RMs: onceCommit'[r]) => tmState' = "commit"
                        
                        /\ tmState' = "abort" => (\A r \in RMs: ~onceCommit'[r])
                        /\ (\E r \in RMs: onceAbort'[r]) => tmState' = "abort"                        
                 BY DEF Itm, Next
    <1>a TypeOK' BY ItmTypeOKInduction
    
    <1>b \A r \in RMs: r \in tmPrepared' => oncePrepare'[r] BY ItmPreparedInduction
    <1>c tmState' = "commit" => RMs = tmPrepared' BY ItmCommitPreparedInduction
    
    <1>d (\E r \in RMs: onceCommit'[r]) => tmState' = "commit" BY ItmCommitCommitInduction
    
    <1>e tmState' = "abort" => (\A r \in RMs: ~onceCommit'[r]) BY ItmAbortNotCommitInduction
    <1>f (\E r \in RMs: onceAbort'[r]) => tmState' = "abort" BY ItmAbortAbortInduction
    <1>. QED BY <1>a, <1>b, <1>c, <1>d, <1>e, <1>f

THEOREM ItmSafety ==
    Itm => ToyR BY DEF Itm, TypeOK, ToyR

=============================================================================
\* Modification History
\* Last modified Tue Jun 10 10:49:39 EDT 2025 by johnnguyen
\* Created Tue Jun 10 10:30:10 EDT 2025 by johnnguyen

----------------------------- MODULE BTMLemmas -----------------------------
EXTENDS BTM

\* Proof left as an exercise for the reader
THEOREM ItmTypeOKInduction ==
    Itm /\ Next => TypeOK'
    <1> SUFFICES ASSUME Itm /\ Next, NEW rm \in RMs,
                        SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm)
                 PROVE TypeOK'
                 BY DEF Next
    <1>a oncePrepare' \in [RMs -> {FALSE, TRUE}]
    <1>b onceCommit \in [RMs -> {FALSE, TRUE}]
    <1>c onceAbort \in [RMs -> {FALSE, TRUE}]
    <1>d tmState' \in {"init", "commit", "abort"}
    <1>e tmPrepared \in SUBSET RMs
    <1>. QED

THEOREM ItmPreparedInduction == 
    Itm /\ Next => \A r \in RMs: r \in tmPrepared' => oncePrepare'[r]
    <1> SUFFICES ASSUME Itm /\ Next, NEW rm \in RMs,
                        SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm)
                 PROVE \A r \in RMs: r \in tmPrepared' => oncePrepare'[r]
                 BY DEF Next
    
    <1>. QED

THEOREM ItmCommitPreparedInduction ==
    Itm /\ Next => (tmState' = "commit" => RMs = tmPrepared') 
    <1> SUFFICES ASSUME Itm /\ Next, NEW rm \in RMs,
                        SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm)
                 PROVE tmState' = "commit" => RMs = tmPrepared'
                 BY DEF Next
    
    <1>. QED   

THEOREM ItmCommitCommitInduction == 
    Itm /\ Next => ((\E r \in RMs: onceCommit'[r]) => tmState' = "commit")
    <1> SUFFICES ASSUME Itm /\ Next, NEW rm \in RMs,
                        SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm)
                 PROVE (\E r \in RMs: onceCommit'[r]) => tmState' = "commit"
                 BY DEF Next
    
    <1>. QED

THEOREM ItmAbortNotCommitInduction == 
    Itm /\ Next => (tmState' = "abort" => (\A r \in RMs: ~onceCommit'[r]))
    <1> SUFFICES ASSUME Itm /\ Next, NEW rm \in RMs,
                        SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm)
                 PROVE tmState' = "abort" => (\A r \in RMs: ~onceCommit'[r])
                 BY DEF Next
    
    <1>. QED

THEOREM ItmAbortAbortInduction == 
    Itm /\ Next => ((\E r \in RMs: onceAbort'[r]) => tmState' = "abort")
    <1> SUFFICES ASSUME Itm /\ Next, NEW rm \in RMs,
                        SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm)
                 PROVE (\E r \in RMs: onceAbort'[r]) => tmState' = "abort"
                 BY DEF Next
    
    <1>. QED

=============================================================================
\* Modification History
\* Last modified Tue Jun 10 14:37:55 EDT 2025 by johnnguyen
\* Created Tue Jun 10 10:30:46 EDT 2025 by johnnguyen

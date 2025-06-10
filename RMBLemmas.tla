----------------------------- MODULE RMBLemmas -----------------------------
EXTENDS RMB


\* TypeOK necessary for rmState' = [rmState EXCEPT ![rm] = "abort"] => rmState'[rm] = "abort"
\* Technicallly speaking, Irm does not imply TypeOK by itself. Nothing stopping onceAbort[rm] = Bagel
LEMMA IrmImpliesAlwaysTypeOK ==
    Irm /\ Next => TypeOK /\ TypeOK'    
    
LEMMA IrmCommitInduction ==
    Irm /\ Next /\ ToyR /\ ToyR' => 
    \A r \in RMs: (onceCommit'[r] <=> rmState'[r] = "commit")
    <1> SUFFICES ASSUME Irm /\ Next /\ ToyR /\ ToyR', NEW rm \in RMs, NEW rm1 \in RMs,
                        SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm) \/ SilentAbortRMB(rm)
                 PROVE onceCommit'[rm1] <=> rmState'[rm1] = "commit"
                 BY DEF Next
    
    <1>a onceCommit'[rm1] => rmState'[rm1] = "commit"
        <2> SUFFICES ASSUME onceCommit'[rm1]
                     PROVE rmState'[rm1] = "commit"
                     OBVIOUS
                     
        <2>a CASE SyncPrepare(rm)
            <3>1 rmState[rm] = "working" BY <2>a DEF SyncPrepare, RM!Prepare
            <3>2 onceCommit[rm1] BY <2>a DEF SyncPrepare, B!Prepare
            <3>3 oncePrepare[rm] BY <3>2 DEF ToyR
            <3>4 rmState[rm] # "working" BY <3>3 DEF Irm
            <3>. QED BY <3>1, <3>4
        
        
        <2>b CASE SyncCommit(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "commit"] BY <2>b DEF SyncCommit, RM!Commit
            <3>2 rm1 = rm \/ rm1 # rm OBVIOUS
            
            <3>a CASE rm1 = rm
                <4>1 rmState'[rm1] = "commit" BY <3>1, <3>a, IrmImpliesAlwaysTypeOK DEF TypeOK
                <4>. QED BY <4>1
                
            <3>b CASE rm1 # rm
                <4>1 onceCommit[rm1] BY <2>b, <3>b DEF SyncCommit, B!Commit
                <4>2 rmState[rm1] = "commit" BY <4>1 DEF Irm
                <4>3 rmState'[rm1] = "commit" BY <3>1, <3>b, <4>2 DEF SyncCommit, RM!Commit
                <4>. QED BY <4>3
                
            <3>. QED BY <3>2, <3>a, <3>b
            
            
        <2>c CASE SyncAbort(rm)
            <3>1 onceAbort' = [onceAbort EXCEPT ![rm] = TRUE] BY <2>c DEF SyncAbort, B!Abort
            <3>2 onceAbort'[rm] = TRUE BY <3>1, IrmImpliesAlwaysTypeOK DEF TypeOK
            <3>3 ~onceCommit'[rm1] BY <3>2 DEF ToyR
            <3>. QED BY <3>3
        
        
        <2>d CASE SilentAbortRMB(rm)
            <3>1 rmState[rm] = "working" BY <2>d DEF SilentAbortRMB, RM!SilentAbort
            <3>2 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <2>d DEF SilentAbortRMB, RM!SilentAbort
            <3>3 oncePrepare'[rm] BY DEF ToyR
            <3>4 oncePrepare[rm] BY <2>d, <3>3 DEF SilentAbortRMB
            <3>5 rmState[rm] # "working" BY <3>4 DEF Irm 
            <3>. QED BY <3>1, <3>5
        
        <2>. QED BY <2>a, <2>b, <2>c, <2>d
    
    <1>b rmState'[rm1] = "commit" => onceCommit'[rm1]
        <2> SUFFICES ASSUME rmState'[rm1] = "commit"
                     PROVE onceCommit'[rm1]
                     OBVIOUS
                     
        <2>a CASE SyncPrepare(rm)
            <3>1 rmState[rm] = "working" BY <2>a DEF SyncPrepare, RM!Prepare
            <3>2 rmState' = [rmState EXCEPT ![rm] = "prepared"] BY <2>a DEF SyncPrepare, RM!Prepare
            <3>3 rmState[rm1] = "commit" BY <3>2
            <3>4 onceCommit[rm1] BY <3>3 DEF Irm
            <3>5 oncePrepare[rm] BY <3>4 DEF ToyR
            <3>6 rmState[rm] # "working" BY <3>5 DEF Irm
            <3>. QED BY <3>1, <3>6
        
        
        <2>b CASE SyncCommit(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "commit"] BY <2>b DEF SyncCommit, RM!Commit
            <3>2 onceCommit' = [onceCommit EXCEPT ![rm] = TRUE] BY <2>b DEF SyncCommit, B!Commit
            <3>3 onceCommit'[rm] BY <3>2, IrmImpliesAlwaysTypeOK DEF TypeOK
            <3>4 rm1 = rm \/ rm1 # rm OBVIOUS
            
            <3>a CASE rm1 = rm
                <4>1 onceCommit'[rm1] BY <3>3, <3>a
                <4>. QED BY <4>1
                
            <3>b CASE rm1 # rm
                <4>1 rmState[rm1] = "commit" BY <3>1, <3>b
                <4>2 onceCommit[rm1] BY <4>1 DEF Irm
                <4>3 onceCommit'[rm1] BY <3>2, <3>b, <4>2
                <4>. QED BY <4>3
            
            <3>. QED BY <3>4, <3>a, <3>b
        
        
        <2>c CASE SyncAbort(rm)
            <3>1 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <2>c DEF SyncAbort, RM!Abort
            <3>2 onceAbort' = [onceAbort EXCEPT ![rm] = TRUE] BY <2>c DEF SyncAbort, B!Abort
            <3>3 onceAbort'[rm] BY <3>2, IrmImpliesAlwaysTypeOK DEF TypeOK
            <3>4 ~onceCommit'[rm1] BY <3>3 DEF ToyR
            <3>5 rmState[rm1] = "commit" BY <3>1
            <3>6 onceCommit[rm1] BY <3>5 DEF Irm
            <3>7 onceCommit'[rm1] BY <2>c, <3>6 DEF SyncAbort, B!Abort
      
            <3>. QED BY <3>3, <3>7
        
        
        <2>d CASE SilentAbortRMB(rm)
            <3>1 rmState[rm] = "working" BY <2>d DEF SilentAbortRMB, RM!SilentAbort
            <3>2 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <2>d DEF SilentAbortRMB, RM!SilentAbort
            <3>3 rmState[rm1] = "commit" BY <3>2
            <3>4 onceCommit[rm1] BY <3>3 DEF Irm
            <3>5 oncePrepare[rm] BY <3>4 DEF ToyR
            <3>6 rmState[rm] # "working" BY <3>5 DEF Irm
            <3>. QED BY <3>1, <3>6
        
        
        <2>. QED BY <2>a, <2>b, <2>c, <2>d
    
    <1>. QED BY <1>a, <1>b


LEMMA IrmPrepareInduction ==
    Irm /\ Next /\ ToyR /\ ToyR' => 
    \A r \in RMs: (oncePrepare'[r] => rmState'[r] # "working")
    <1> SUFFICES ASSUME Irm /\ Next /\ ToyR /\ ToyR', NEW rm \in RMs, NEW rm1 \in RMs, 
                        SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm) \/ SilentAbortRMB(rm)
                 PROVE oncePrepare'[rm1] => rmState'[rm1] # "working"
                 BY DEF Next
                 
    <1> SUFFICES ASSUME oncePrepare'[rm1]
                 PROVE rmState'[rm1] # "working"
                 OBVIOUS
                 
    <1>a CASE SyncPrepare(rm)
        <2>1 rmState[rm] = "working" BY <1>a DEF SyncPrepare, RM!Prepare
        <2>2 oncePrepare' = [oncePrepare EXCEPT ![rm] = TRUE] BY <1>a DEF SyncPrepare, B!Prepare
        <2>3 oncePrepare'[rm] BY <2>2, IrmImpliesAlwaysTypeOK DEF TypeOK
        <2>4 rmState' = [rmState EXCEPT ![rm] = "prepared"] BY <1>a DEF SyncPrepare, RM!Prepare
        <2>5 rmState'[rm] = "prepared" BY <2>4, IrmImpliesAlwaysTypeOK DEF TypeOK
        <2>6 rm1 = rm \/ rm1 # rm OBVIOUS
        
        <2>7 CASE rm1 = rm
            <3>. QED BY <2>7, <2>5
            
        <2>8 CASE rm1 # rm
            <3>1 oncePrepare' = [oncePrepare EXCEPT ![rm] = TRUE] BY <1>a DEF SyncPrepare, B!Prepare
            <3>2 oncePrepare[rm1] BY <2>8, <3>1
            <3>3 rmState[rm1] # "working" BY <3>2 DEF Irm
            <3>4 rmState' = [rmState EXCEPT ![rm] = "prepared"] BY <1>a DEF SyncPrepare, RM!Prepare
            <3>5 rmState'[rm1] # "working" BY <2>8, <3>3, <3>4
            <3>. QED BY <3>5
        <2>. QED BY <2>7, <2>8
        
        
    <1>b CASE SyncCommit(rm)
        <2>1 onceCommit' = [onceCommit EXCEPT ![rm] = TRUE] BY <1>b DEF SyncCommit, B!Commit
        <2>2 onceCommit'[rm] BY <2>1, IrmImpliesAlwaysTypeOK DEF TypeOK
        <2>3 oncePrepare'[rm1] BY <2>2 DEF ToyR
        <2>4 oncePrepare[rm1] BY <1>b, <2>3 DEF SyncCommit, B!Commit
        <2>5 rmState[rm1] # "working" BY <2>4 DEF Irm
        <2>6 rmState' = [rmState EXCEPT ![rm] = "commit"] BY <1>b DEF SyncCommit, RM!Commit
        <2>7 rmState'[rm1] # "working" \/ rmState'[rm1] = "commit" BY <2>5, <2>6
        
        <2>. QED BY <2>7
    
    
    <1>c CASE SyncAbort(rm)
        <2>1 oncePrepare[rm1] BY <1>c DEF SyncAbort, B!Abort
        <2>2 rmState[rm1] # "working" BY <2>1 DEF Irm
        <2>3 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <1>c DEF SyncAbort, RM!Abort
        <2>4 rmState'[rm1] # "working" \/ rmState'[rm1] = "abort" BY <2>2, <2>3
        
        <2>. QED BY <2>4
    
    
    <1>d CASE SilentAbortRMB(rm)
        <2>1 rmState[rm] = "working" BY <1>d DEF SilentAbortRMB, RM!SilentAbort
        <2>2 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <1>d DEF SilentAbortRMB, RM!SilentAbort
        <2>3 oncePrepare[rm1] BY <1>d DEF SilentAbortRMB
        <2>4 rmState[rm1] # "working" BY <2>3 DEF Irm
        <2>5 rmState'[rm1] # "working" \/ rmState'[rm1] = "abort" BY <2>2, <2>4
        
        <2>. QED BY <2>5
    
    
    <1>. QED BY <1>a, <1>b, <1>c, <1>d
    
    
\* Investigate this schema to solve issues in SyncPrepare. UPDATE: Schema works
\* <2>4 rm1 = rm \/ rmState'[rm1] = rmState[rm1] BY <2>3
LEMMA IrmAbortInduction ==
    Irm /\ Next /\ ToyR /\ ToyR' => 
    \A r \in RMs: ((oncePrepare'[r] /\ rmState'[r] = "abort") => onceAbort'[r])
    <1> SUFFICES ASSUME Irm /\ Next /\ ToyR /\ ToyR', NEW rm \in RMs, NEW rm1 \in RMs, 
                       SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm) \/ SilentAbortRMB(rm)
                 PROVE (oncePrepare'[rm1] /\ rmState'[rm1] = "abort") => onceAbort'[rm1]
                 BY DEF Next
    
    <1> SUFFICES ASSUME (oncePrepare'[rm1] /\ rmState'[rm1] = "abort")
                 PROVE onceAbort'[rm1]
                 OBVIOUS
                              
    <1>a CASE SyncPrepare(rm)
        <2>1 rmState' = [rmState EXCEPT ![rm] = "prepared"] BY <1>a DEF SyncPrepare, RM!Prepare
        <2>2 oncePrepare' = [oncePrepare EXCEPT ![rm] = TRUE] BY <1>a DEF SyncPrepare, B!Prepare
        <2>3 rm1 = rm \/ rm1 # rm OBVIOUS
        
        <2>4 CASE rm1 = rm
            <3>1 rmState'[rm1] = "prepared" BY <1>a, <2>4 DEF SyncPrepare, RM!Prepare
            <3>. QED BY <3>1
            
        <2>5 CASE rm1 # rm
            <3>1 rmState[rm1] = "abort" BY <2>1, <2>5
            <3>2 oncePrepare[rm1] BY <2>2, <2>5
            <3>3 onceAbort[rm1] BY <3>1, <3>2 DEF Irm
            <3>4 onceAbort'[rm1] BY <1>a, <3>3 DEF SyncPrepare, B!Prepare
            <3>. QED BY <3>4

        <2>. QED BY <2>4, <2>5
    
    
    <1>b CASE SyncCommit(rm)
        <2>1 oncePrepare[rm1] BY <1>b DEF SyncCommit, B!Commit 
        <2>2 rmState' = [rmState EXCEPT ![rm] = "commit"] BY <1>b DEF SyncCommit, RM!Commit
        <2>3 rmState[rm1] = "abort" BY <2>2
        <2>4 onceAbort[rm1] BY <2>1, <2>3 DEF Irm
        <2>5 onceAbort'[rm1] BY <1>b, <2>4 DEF SyncCommit, B!Commit
    
        <2>. QED BY <2>5
    
    
    <1>c CASE SyncAbort(rm)
        <2>1 onceAbort' = [onceAbort EXCEPT ![rm] = TRUE] BY <1>c DEF SyncAbort, B!Abort
        <2>2 oncePrepare[rm1] BY <1>c DEF SyncAbort, B!Abort
        <2>3 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <1>c DEF SyncAbort, RM!Abort
        <2>4 rm1 = rm \/ rmState'[rm1] = rmState[rm1] BY <2>3
        <2>5 rm1 = rm => onceAbort'[rm1] = onceAbort'[rm] OBVIOUS
        
        <2>a CASE rm1 = rm 
            <3>1 onceAbort'[rm] BY <2>1, IrmImpliesAlwaysTypeOK DEF TypeOK
            <3>2 onceAbort'[rm1] BY <2>a, <3>1
            <3>. QED BY <3>2
            
        <2>b CASE rmState'[rm1] = rmState[rm1]
            <3>1 rmState[rm1] = "abort" BY <2>b
            <3>2 onceAbort[rm1] BY <2>2, <3>1 DEF Irm
            <3>3 onceAbort'[rm1] BY <1>c, <3>2 DEF SyncAbort, B!Abort
            <3>. QED BY <3>3
        
        <2>. QED BY <2>4, <2>a, <2>b
    
    
    <1>d CASE SilentAbortRMB(rm)
        <2>1 oncePrepare[rm1] BY <1>d DEF SilentAbortRMB
        <2>2 rmState[rm1] # "working" BY <2>1 DEF Irm
        <2>3 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <1>d DEF SilentAbortRMB, RM!SilentAbort
        <2>4 rmState[rm] = "working" BY <1>d DEF SilentAbortRMB, RM!SilentAbort
        <2>5 rmState[rm1] = "abort" BY <2>2, <2>3, <2>4
        <2>6 onceAbort[rm1] BY <2>1, <2>5 DEF Irm
        <2>7 onceAbort'[rm1] BY <1>d, <2>6 DEF SilentAbortRMB
        
        <2>. QED BY <2>7
    
    
    <1>. QED BY <1>a, <1>b, <1>c, <1>d


\* !!!RELIES ON IrmCommitInduction!!!
LEMMA IrmConsistentInduction ==
    Irm /\ Next /\ ToyR /\ ToyR' => Consistent'
    <1> SUFFICES ASSUME Irm /\ ToyR /\ ToyR', NEW rm\in RMs, NEW rm1 \in RMs, NEW rm2 \in RMs, Next, \* helps for proof
                        SyncPrepare(rm) \/ SyncCommit(rm) \/ SyncAbort(rm) \/ SilentAbortRMB(rm)
                 PROVE ~(rmState'[rm1] = "abort" /\ rmState'[rm2] = "commit")
                 BY DEF Next, Consistent
    \* Could embed this in previous SUFFICES ASSUME, but I like that this makes the direction clear
    <1>1 SUFFICES ASSUME rmState'[rm1] = "abort" /\ rmState'[rm2] = "commit"
                 PROVE FALSE
                 OBVIOUS
                 
    <1>a CASE SyncPrepare(rm)
        <2>1 rmState' = [rmState EXCEPT ![rm] = "prepared"] BY <1>a DEF SyncPrepare, RM!Prepare
        <2>2 rmState[rm2] = "commit" BY <1>1, <2>1
        <2>3 rmState[rm1] = "abort" BY <1>1, <2>1
        <2>. QED BY <2>2, <2>3 DEF Irm, Consistent
        
        
    <1>b CASE SyncCommit(rm)
        <2>1 rmState' = [rmState EXCEPT ![rm] = "commit"] BY <1>b DEF SyncCommit, RM!Commit
        <2>2 rmState[rm1] = "abort" BY <1>1, <2>1
        <2>3 onceCommit'[rm2] BY <1>1, IrmCommitInduction 
        <2>4 oncePrepare'[rm1] BY <2>3 DEF ToyR
        <2>5 oncePrepare[rm1] BY <1>b, <2>4 DEF SyncCommit, B!Commit
        <2>6 onceAbort[rm1] BY <2>2, <2>5 DEF Irm
        <2>7 onceAbort'[rm1] BY <1>b, <2>6 DEF SyncCommit, B!Commit 
        <2>8 ~onceCommit'[rm2] BY <2>7 DEF ToyR
        <2>. QED BY <2>3, <2>8
        
        
    <1>c CASE SyncAbort(rm)
        <2>1 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <1>c DEF SyncAbort, RM!Abort
        <2>2 onceAbort' = [onceAbort EXCEPT ![rm] = TRUE] BY <1>c DEF SyncAbort, B!Abort
        <2>3 onceAbort'[rm] BY <2>2, IrmImpliesAlwaysTypeOK DEF TypeOK
        <2>4 ~onceCommit'[rm2] BY <2>3 DEF ToyR
        <2>5 ~onceCommit[rm2] BY <1>c, <2>4 DEF SyncAbort, B!Abort
        <2>6 rmState[rm2] # "commit" BY <2>5 DEF Irm
        <2>7 rmState[rm2] = "commit" BY <1>1, <2>1
        <2>. QED BY <2>6, <2>7
        
    
    <1>d CASE SilentAbortRMB(rm)
        <2>1 rmState[rm] = "working" BY <1>d DEF SilentAbortRMB, RM!SilentAbort
        <2>2 rmState' = [rmState EXCEPT ![rm] = "abort"] BY <1>d DEF SilentAbortRMB, RM!SilentAbort
        <2>3 rmState[rm2] = "commit" BY <1>1, <2>2
        <2>4 onceCommit[rm2] BY <2>3 DEF Irm
        <2>5 oncePrepare[rm] BY <2>4 DEF ToyR
        <2>6 rmState[rm] # "working" BY <2>5 DEF Irm     
        <2>. QED BY <2>1, <2>6
    
    <1>. QED BY <1>a, <1>b, <1>c, <1>d

=============================================================================
\* Modification History
\* Last modified Sun Jun 08 17:52:53 EDT 2025 by johnnguyen
\* Created Fri Jun 06 15:59:35 EDT 2025 by johnnguyen

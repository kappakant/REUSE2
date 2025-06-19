------------------------ MODULE ToyTMCariniTheorems ------------------------
\* Prove that the candidate inductive invariant selected by carini is indeed inductive and invariant
EXTENDS ToyTMCarini

(***************************************************************************
CandSep ==
/\ \A var0 \in RMs : (onceAbort14[var0]) => (~(lastCommit15[var0]))
/\ \A var0 \in RMs : (lastCommit6[var0]) => (oncePrepare7[var0])
/\ \A var0 \in RMs : (onceCommit17[var0]) => (~(onceAbort18[var0]))
 ***************************************************************************)

THEOREM CandSepInitiation ==
    Init => CandSep
    
THEOREM CandSepConsecution ==
    CandSep /\ Next => CandSep'
    
\* Don't need safety, this is just the helper module
(***************************************************************************
THEOREM CandSepSafety ==
    CandSep => Consistent
 ***************************************************************************)
 
=============================================================================
\* Modification History
\* Last modified Thu Jun 12 09:33:25 EDT 2025 by johnnguyen
\* Created Wed Jun 11 22:33:33 EDT 2025 by johnnguyen

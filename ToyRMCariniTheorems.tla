------------------------ MODULE ToyRMCariniTheorems ------------------------
\* We have CandSep now, now we prove that <CandSep>C<Consistent> by finding eligible Inv?
EXTENDS ToyRMCarini

Inv == TRUE
\* do this for all of them
THEOREM InvInitiation ==
    Init /\ CandSep => Inv

THEOREM InvConsecution ==
    Inv /\ Next /\ CandSep /\ CandSep' => Inv'
    
THEOREM InvSafety ==
    Inv => Consistent

=============================================================================
\* Modification History
\* Last modified Thu Jun 12 11:50:47 EDT 2025 by johnnguyen
\* Created Thu Jun 12 09:29:38 EDT 2025 by johnnguyen

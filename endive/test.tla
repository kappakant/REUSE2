---- MODULE msgs_tmState_hist_CTIGen_1928 ----
EXTENDS msgs_tmState_hist

Inv0_1_0 == \A rmi \in RMs : \A rmj \in RMs : (Fluent17_0[rmi]) \/ ((Fluent17_0[rmj]))
Inv71_1_0 == \A rmi \in RMs : \A rmj \in RMs : (Fluent18_0[rmi]) \/ ((Fluent18_0[rmj]))
InvStrengthened ==
    /\ CandSep
    /\ Inv0_1_0
    /\ Inv71_1_0

IndCand ==
    /\ TypeOK
    /\ InvStrengthened
====
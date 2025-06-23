---- MODULE msgs_tmState_hist_CTIGen_30 ----
EXTENDS msgs_tmState_hist

Inv123_1_0 == \A rmi \in RMs : \A rmj \in RMs : (Fluent18_0[rmj]) \/ ((msgs = {}))
Inv15_1_0 == \A rmi \in RMs : \A rmj \in RMs : (Fluent17_0[rmi]) \/ ((msgs = {}))
Inv107_1_0 == \A rmi \in RMs : \A rmj \in RMs : (Fluent18_0[rmi]) \/ (~(msgs = {}))
Inv34_1_0 == \A rmi \in RMs : \A rmj \in RMs : (Fluent17_0[rmi]) \/ (~(msgs = {}))
InvStrengthened ==
    /\ CandSep
    /\ Inv123_1_0
    /\ Inv15_1_0
    /\ Inv107_1_0
    /\ Inv34_1_0

IndCand ==
    /\ TypeOK
    /\ InvStrengthened
====
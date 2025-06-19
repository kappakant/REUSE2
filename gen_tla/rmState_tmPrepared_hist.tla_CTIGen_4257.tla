---- MODULE rmState_tmPrepared_hist.tla_CTIGen_4257 ----
EXTENDS rmState_tmPrepared_hist.tla

InvStrengthened ==
    /\ Consistent

IndCand ==
    /\ TypeOK
    /\ InvStrengthened
====
---- MODULE rmState_tmPrepared_hist.tla_CTIGen_6742 ----
EXTENDS rmState_tmPrepared_hist.tla

InvStrengthened ==
    /\ Consistent

IndCand ==
    /\ TypeOK
    /\ InvStrengthened
====
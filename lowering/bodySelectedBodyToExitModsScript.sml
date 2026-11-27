(* Lift the reached body outcome to the qualified callee-exit post.  The
   execution and suffix leaves provide the two post-transform callbacks; this
   satellite only performs the common gas-outcome transport. *)
Theory bodySelectedBodyToExitMods
Ancestors
  gasOutcomeFullPostMods bodyFullIntCallDefs bodyIntCallSeams
  bodySelectedCalleeCodeCutsMods bodySelectedLockedFragMods
  bodySelectedLockedGuardsMods bodySelectedLockedReplayMods
  bodyFullPostsMods bodyFullPredsMods

Theorem selected_body_to_callee_exit_mods:
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (intcall_callee_src cx name mut nr ss)
    (es,entered,FEMPTY,tn) Q R /\
  (!H res ee G' tn' t.
     (?xs. !tail. intcall_callee_src cx name mut nr ss
         (es with gas_obs := xs ++ tail) = (res,ee with gas_obs := tail)) /\
     ee.gas_obs = [] /\ ~t.vs_halted /\
     valid_horizon cx st0 H ee.storage_trace /\
     Q H res ee G' tn' t ==> Q' H res ee G' tn' t) /\
  (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
    (intcall_callee_src cx name mut nr ss)
    (es,entered,FEMPTY,tn) Q' R'
Proof
  strip_tac >> irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`Q`,`R`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

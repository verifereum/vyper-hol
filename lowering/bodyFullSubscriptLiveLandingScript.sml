(* A live array selector returns or aborts without consuming a GAS mark.
   Keep the source equation and a single result and ghost pair, rather than
   committing the witness to a particular outcome constructor. *)
Theory bodyFullSubscriptLiveLanding
Ancestors
  gasOutcomeFullCompose gasSummary fragGasOriginPtr fragExec vyperStorageFootprint
  vyperState

Definition live_select_landing_def:
  live_select_landing (DF,lo,E,C,f,PG) cx st0 source (fin,s,G,tn) Q R certifies <=>
    ?res r G' tn'.
      certifies r /\
      (!tail. source (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
      storage_trace_domain cx st0 fin.storage_trace /\
      !H. valid_horizon cx st0 H fin.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (r,G',tn') /\
        ((?t. r = OK t /\ Q H res (fin with gas_obs := []) G' tn' t) \/
         (exit_result r /\ R H res (fin with gas_obs := []) (G',tn') r))
End

Theorem live_select_landing_full:
  live_select_landing (DF,lo,E,C,f,PG) cx st0 source (fin,s,G,tn) Q R certifies ==>
  gas_outcome_full (DF,lo,E,C,f,PG) tops cx st0 source (fin,s,G,tn) Q R
Proof
  rw[live_select_landing_def] >>
  irule gas_outcome_full_intro >>
  qexistsl [`G'`,`fin`,`[]`,`r`,`res`,`tn'`] >>
  simp[gas_explicit_def]
QED

Theorem live_select_landing_ok:
  certifies (OK t) /\
  (!tail. source (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
  storage_trace_domain cx st0 fin.storage_trace /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (OK t,G',tn') /\
    Q H res (fin with gas_obs := []) G' tn' t) ==>
  live_select_landing (DF,lo,E,C,f,PG) cx st0 source (fin,s,G,tn) Q R certifies
Proof
  rw[live_select_landing_def] >> metis_tac[]
QED

Theorem live_select_landing_exit:
  certifies r /\
  (!tail. source (fin with gas_obs := tail) = (res,fin with gas_obs := tail)) /\
  storage_trace_domain cx st0 fin.storage_trace /\ exit_result r /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (r,G',tn') /\
    R H res (fin with gas_obs := []) (G',tn') r) ==>
  live_select_landing (DF,lo,E,C,f,PG) cx st0 source (fin,s,G,tn) Q R certifies
Proof
  rw[live_select_landing_def] >> metis_tac[]
QED

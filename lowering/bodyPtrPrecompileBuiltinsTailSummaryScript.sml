Theory bodyPtrPrecompileBuiltinsTailSummary
Ancestors gasSummaryComposePtr fragGasPathPtr vyperState list

Theorem pointer_outcome_no_source_read:
  (!tail. source (es with gas_obs := tail) = (res, fin with gas_obs := tail)) /\
  gas_path_ptr D 0 ctx fn PG G0 tn0 s n G tn r /\
  ((?t. r = OK t /\ Q res (fin with gas_obs := []) G tn t) \/
   (exit_result r /\ R res (fin with gas_obs := []) (G,tn) r)) ==>
  gas_outcome_ptr D tops (ctx,fn) PG source (es,s,G0,tn0) Q R
Proof
  strip_tac >>
  `gas_marked_exec_ptr D (ctx,fn) PG source (es,s,G0,tn0)
     (REPLICATE n F) res fin G tn r` by
    (irule gas_marked_exec_ptr_no_source_read >> simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists `REPLICATE n F` >>
  disj1_tac >> rewrite_tac[gas_summary_ptr_at_marked] >>
  goal_assum (drule_at Any) >> simp[]
QED

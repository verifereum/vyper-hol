Theory bodyPtrPrecompileBuiltinsTailSummary
Ancestors gasSummaryComposePtr fragGasPathPtr vyperState list
          exprSimECArith vyperInterpreter

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

Theorem ec_source_tail_gas_obs:
  ec_source_tail cx ann bt tys vs es = (r,es') ==>
  ec_source_tail cx ann bt tys vs (es with gas_obs := g) =
    (r,es' with gas_obs := g)
Proof
  simp[ec_source_tail_def] >>
  Cases_on `builtin_result cx es.accounts ann bt tys vs` >> simp[] >>
  simp[ignore_bind_def, bind_def, precompile_call_success_def] >>
  Cases_on `precompile_builtin bt` >> simp[return_def] >>
  Cases_on `es.outcomes` >> simp[return_def] >>
  rename1 `es.outcomes = SOME outs` >> Cases_on `outs` >>
  simp[check_def, assert_def, raise_def, return_def] >>
  Cases_on `call_outcome_success h` >>
  simp[check_def, assert_def, raise_def, return_def] >>
  strip_tac >> gvs[]
QED

Theorem ec_source_tail_pointer_outcome:
  ec_source_tail cx ann bt tys vs es = (res,fin) /\
  gas_path_ptr D 0 ctx fn PG G0 tn0 s n G tn r /\
  ((?t. r = OK t /\ Q res (fin with gas_obs := []) G tn t) \/
   (exit_result r /\ R res (fin with gas_obs := []) (G,tn) r)) ==>
  gas_outcome_ptr D tops (ctx,fn) PG (ec_source_tail cx ann bt tys vs)
    (es,s,G0,tn0) Q R
Proof
  strip_tac >> irule pointer_outcome_no_source_read >>
  drule ec_source_tail_gas_obs >> strip_tac >>
  metis_tac[]
QED

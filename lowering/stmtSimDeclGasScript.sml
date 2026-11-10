(* Counted sequencing boundaries for declarations. *)
Theory stmtSimDeclGas
Ancestors
  stmtSimDeclSource gasExemptCert gasExemptOrigin gasNormalPrefix gasSummary
  gasSummaryCompose fragGasMode loweringPosts exprLoweringProps vyperState
Libs
  monadsyntax

Theorem stmt_state_rel_start_gas_obs[local]:
  stmt_state_rel ctx func cenv cx (es with gas_obs := gs) s =
  stmt_state_rel ctx func cenv cx es s
Proof
  simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_gas_obs,
       immutable_alloca_sep_def]
QED

Theorem gas_value_prefix_start_gas_obs:
  gas_value_prefix memory (ctx,func,cenv,cx) (ty,e) (sa,sb,op)
    (es,s0) marks out ==>
  gas_value_prefix memory (ctx,func,cenv,cx) (ty,e) (sa,sb,op)
    (es with gas_obs := gs,s0) marks out
Proof
  PairCases_on `out` >>
  simp[gas_value_prefix_def, gas_marked_exec_def, expr_post_def,
       locals_kept_def, stmt_state_rel_start_gas_obs] >>
  strip_tac >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem gas_marked_exec_start_gas_obs[local]:
  gas_marked_exec memory (ctx,func) source (es with gas_obs := gs,s0)
    marks res ee r =
  gas_marked_exec memory (ctx,func) source (es,s0) marks res ee r
Proof
  simp[gas_marked_exec_def]
QED

Theorem gas_exempt_cert_start_gas_obs:
  !memory tops env source start marks out endpoint.
    gas_exempt_cert memory tops env source start marks out endpoint ==>
    !gs. gas_exempt_cert memory tops env source
      (FST start with gas_obs := gs, SND start) marks out endpoint
Proof
  ho_match_mp_tac gas_exempt_cert_ind >> rpt strip_tac >> simp[]
  >- (irule gas_exempt_cert_origin >>
      fs[gas_exempt_origin_def] >>
      drule gas_value_prefix_start_gas_obs >>
      disch_then (qspec_then `gs` assume_tac) >> metis_tac[]) >>
  fs[]
  >- metis_tac[gas_exempt_cert_bind_unit, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_error_unit]
  >- metis_tac[gas_exempt_cert_bind_bool, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_error_bool]
  >- metis_tac[gas_exempt_cert_bind_result, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_error_result]
  >- metis_tac[gas_exempt_cert_bind_value, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_error_value]
  >- metis_tac[gas_exempt_cert_bind_place, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_error_place]
  >- metis_tac[gas_exempt_cert_bind_values, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_error_values]
  >- metis_tac[gas_exempt_cert_bind_results, gas_marked_exec_start_gas_obs]
  >- metis_tac[gas_exempt_cert_error_results]
  >- (irule gas_exempt_cert_cleanup >> qexists `mid` >> simp[])
  >- (irule gas_exempt_cert_handler >> qexists `mid` >> simp[])
  >- (irule gas_exempt_cert_get_scopes >> simp[])
  >- metis_tac[gas_exempt_cert_invoke]
  >> metis_tac[gas_exempt_cert_unforce_result]
QED

Theorem gas_marked_return_prefix[local]:
  gas_marked_path F ctx func s0 0 (OK s1) ==>
  gas_marked_exec F (ctx,func) (return ()) (es,s0) [] (INL ()) es (OK s1)
Proof
  simp[gas_marked_exec_def, return_def]
QED

Theorem gas_exempt_cert_zero_prefix:
  gas_marked_path F ctx func s0 0 (OK s1) /\
  gas_exempt_cert F tops (ctx,func) source (es,s1) marks (err,ee) (leaf,finish_state) ==>
  gas_exempt_cert F tops (ctx,func) source (es,s0) marks (err,ee) (leaf,finish_state)
Proof
  strip_tac >> drule gas_marked_return_prefix >>
  disch_then (qspec_then `es` assume_tac) >>
  drule gas_exempt_cert_start_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >> fs[] >>
  drule gas_exempt_cert_bind_unit >>
  disch_then (qspecl_then [`tops`, `\u. source`] mp_tac) >>
  simp[bind_return] >> disch_then irule >> simp[]
QED

Theorem gas_marked_exec_zero_prefix:
  gas_marked_path F ctx func s0 0 (OK s1) /\
  gas_marked_exec F (ctx,func) source (es,s1) marks res ee r ==>
  gas_marked_exec F (ctx,func) source (es,s0) marks res ee r
Proof
  strip_tac >>
  `s1.vs_gas_readings = s0.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  fs[gas_marked_exec_def] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem annassign_exempt_cert:
  evaluate_type (get_tenv cx) typ = SOME tyv /\
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s) marks (err,ee) (leaf,finish_state) ==>
  gas_exempt_cert F tops (ctx,func) (eval_stmt cx (AnnAssign id typ e))
    (es,s) marks (err,ee) (leaf,finish_state)
Proof
  strip_tac >> drule eval_annassign_action >>
  disch_then (qspecl_then [`id`, `e`] SUBST1_TAC) >>
  irule gas_exempt_cert_error_value >> simp[]
QED

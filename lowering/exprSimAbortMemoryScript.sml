(* Forcing an expression that cannot produce a successful source value. *)
Theory exprSimAbortMemory
Ancestors
  exprSimMemDefs exprSimUnwrap exprSimDefs loweringPosts gasOutcome
  exprLowering compileEnv vyperInterpreter vyperState
  gasSummary gasSummaryCompose gasExemptCert fragGasMode fragGasPath
  exprLoweringProps exprSimProps exprSimMemorySource exprSimUnwrapProps fragExec

Theorem expr_sim_mem_of_aborting_vv:
  expr_vv_sim_mem ctx func cenv cx ty e es /\
  (!s v s'. eval_expr cx e s <> (INL v,s')) ==>
  expr_sim_mem ctx func cenv cx ty e es
Proof
  rw[expr_sim_mem_def] >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv, sm)` >>
  simp[] >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule unwrap_value_extends >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `sm`, `vv`, `s0`] mp_tac) >> simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac >> qexists_tac `marks`
  >- (disj1_tac >> gvs[gas_summary_at_def]
      >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
            (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
          strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
          simp[] >> metis_tac[]) >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e'` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  disj2_tac >> metis_tac[force_exempt_cert]
QED

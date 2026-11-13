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
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `vv`, `s0`] mp_tac) >> simp[] >>
  rewrite_tac[gas_outcome_def] >> BETA_TAC >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists_tac `marks` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_bind_left >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `es_end`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disch_then kall_tac >> qexists_tac `marks` >> disj1_tac >>
          irule gasStorageTheory.gas_bad_storage_at_bind_left >>
          simp[vyperStorageTraceTheory.storage_trace_frame_read_result] >>
          irule gasStorageTheory.gas_bad_storage_at_counted_prefix >>
          metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by
        fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN (strip_assume_tac o BETA_RULE))
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          first_x_assum drule >> strip_tac >>
          qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
            (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
          strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
          gvs[] >> metis_tac[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `expr_exit res r` by metis_tac[] >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >> BETA_TAC >>
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
  strip_tac >> qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  metis_tac[force_exempt_cert]
QED

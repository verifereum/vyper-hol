Theory externalReturnIntcallForce
Ancestors
  externalReturnIntcallProducer externalReturnVvPrefixProbe
  exprSimMemoryForce exprSimMemoryRead exprSimMemorySource exprSimDefs
  exprSimUnwrapProps
  exprLowering exprLoweringProps loweringPosts compileEnv
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext gasStorage
  vyperStorageTrace vyperStorageFootprint
  fragGasPath fragGasMode fragExec vyperAST vyperInterpreter vyperState

Theorem return_intcall_located_force:
  compile_expr ce ct (Call ann (IntCall fid) args drv) sa =
    (LocatedValue ty p,sm) /\
  unwrap_value ce (LocatedValue ty p) sm = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  expr_vv_sim ctx func ce cx ct (Call ann (IntCall fid) args drv) es /\
  gas_admissible
    (eval_stmt cx (Return (SOME (Call ann (IntCall fid) args drv))))
    (stmt_res_ok lctx) es /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s0 /\
     storage_well_formed_on cx es (FST H)) /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (eval_expr cx (Call ann (IntCall fid) args drv)) (read_result cx))
    (es,s0)
    (\H res ee s. ?v. res = INL v /\
      ty = ce.ce_func_return_type (nsid_to_string fid) /\
      p.ptr_location = LocMemory /\
      expr_post H ctx func ce cx (Call ann (IntCall fid) args drv)
        es sa sb s0 ee v op s /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\H res ee r. expr_exit res r)
Proof
  strip_tac >>
  drule return_compile_intcall_output >> simp[] >> strip_tac >> gvs[] >>
  `lower_value compile_expr ce ct (Call ann (IntCall fid) args drv) sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def] >>
  drule_all return_lower_value_code_slices >> strip_tac >> gvs[] >>
  drule_all return_site_vv_admissible >> strip_tac >>
  drule_all return_vv_located_prefix >>
  rewrite_tac[gas_outcome_def] >> BETA_TAC >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN mp_tac))
  >- (strip_tac >> qexists_tac `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >>
      simp[storage_trace_frame_read_result]) >>
  disch_then (DISJ_CASES_THEN mp_tac)
  >- (rewrite_tac[gas_summary_at_def] >>
      disch_then (qx_choose_then `res` (qx_choose_then `es_end`
        (qx_choose_then `r` (CONJUNCTS_THEN2 assume_tac mp_tac)))) >>
      reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
      >- (disch_then kall_tac >> qexists_tac `marks` >> disj1_tac >>
          irule gas_bad_storage_at_bind_left >>
          simp[storage_trace_frame_read_result] >>
          irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by fs[storage_trace_domain_def] >>
      disch_then (DISJ_CASES_THEN (strip_assume_tac o BETA_RULE)) >>
      qexists_tac `marks` >> disj2_tac >> disj1_tac >>
      rewrite_tac[gas_summary_at_def] >> BETA_TAC
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
            (assume_tac o SIMP_RULE (srw_ss()) []) >>
          first_assum (drule_then strip_assume_tac) >> gvs[] >>
          `~t.vs_halted` by
            metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
          drule_all unwrap_memory_marked_read_horizons >> strip_tac >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK u`] >>
          simp[expr_type_def] >>
          `marks = marks ++ []` by simp[] >>
          pop_assum SUBST1_TAC >> irule gas_marked_exec_bind_normal >>
          goal_assum drule >> simp[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `expr_exit res r` by metis_tac[] >>
      Cases_on `res`
      >- (Cases_on `r` >> gvs[expr_exit_def]) >>
      rename1 `expr_exit (INR exc) r` >>
      `expr_res_ok (INR exc : value + exception)` by
        (Cases_on `exc` >> Cases_on `r` >>
         gvs[expr_exit_def, expr_res_ok_def, AllCaseEqs()] >>
         Cases_on `e` >> gvs[expr_exit_def, expr_res_ok_def]) >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      simp[GSYM expr_exit_exception_transport] >>
      irule gas_marked_exec_bind_exception >> goal_assum drule) >>
  strip_tac >> qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  metis_tac[force_exempt_cert]
QED

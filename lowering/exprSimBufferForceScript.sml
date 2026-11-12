(* Counted forcing of an allocated nonword memory buffer. *)
Theory exprSimBufferForce
Ancestors
  exprSimMemorySource exprSimUnwrapProps exprSimProps exprSimDefs
  loweringPosts gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  gasStorage vyperStorageTrace vyperStorageFootprint
  fragGasPath fragGasMode exprLowering exprLoweringProps compileEnv
  vyperAST vyperInterpreter vyperState venomState list finite_map
Libs
  monadsyntax

(* Memory-buffer forcing uses only the oracle-clean memory boundary. *)
Theorem expr_sim_of_vv_sim_buffer:
  !ctx func cenv cx ty e es.
    expr_vv_sim ctx func cenv cx ty e es /\
    (!sa. ?t p sb. compile_expr cenv ty e sa = (LocatedValue t p,sb) /\
      p.ptr_location = LocMemory /\ ~is_word_type t) /\
    (!tv es'. eval_expr cx e es = (INL tv,es') ==> ?v. tv = Value v) ==>
    expr_sim ctx func cenv cx ty e es
Proof
  rw[expr_sim_def] >>
  qpat_x_assum `!tv es'. eval_expr _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `!sa. ?t p sb. _` (qspec_then `sa` strip_assume_tac) >>
  drule_all lower_value_nonword_memory >> strip_tac >> gvs[] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim _ _ _ _ _ _ _` mp_tac >>
  simp[expr_vv_sim_def] >>
  disch_then (qspecl_then [`st0`, `sa`, `sb`, `LocatedValue t p`, `s0`] mp_tac) >>
  simp[] >>
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
          `?v. read_result cx tv (es_end with gas_obs := []) =
               (INL v, es_end with gas_obs := [])` by
            (qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
               (drule_then mp_tac) >>
             simp[vv_post_def, vv_holds_def] >> metis_tac[]) >>
          qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK t'`] >>
          simp[] >> conj_tac
          >- (drule read_result_gas_obs >> strip_tac >>
              gvs[gas_marked_exec_def, bind_def]) >>
          rpt strip_tac >> irule expr_post_of_vv_post_memory >> simp[] >>
          qexists_tac `t` >> simp[] >>
          irule vv_post_read_result >> simp[] >> metis_tac[]) >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> _`
        (assume_tac o SIMP_RULE (srw_ss()) []) >>
      `expr_exit res r` by metis_tac[] >>
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

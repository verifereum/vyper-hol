(* Counted valued returns in the selected external frame. *)
Theory externalReturnValuedFrag
Ancestors externalReturnSelectedDispatch externalReturnSelectedResources
  externalReturnSelectedPrefix
  externalReturnCountedBoundary externalReturnConsumerFit
  stmtLoweringMono stmtSimDefs loweringPosts bodySim exprSimHypsDefs
  exprLoweringProps fragExec compileEnv stmtLowering

Theorem return_selected_valued_frag:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops ut nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  get_tenv cx = type_env tops /\
  expr_sim_inv ce cx env es /\ stmt_exprs_ok ce (Return (SOME e)) /\
  IS_SOME (type_stmt env ret (Return (SOME e))) /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (!ty. expr_sim ctx func ce cx ty e es /\ expr_vv_sim ctx func ce cx ty e es) /\
  ce.ce_raw_return = lookup_raw_return_or_F (NONE:num option)
    tx.function_name External tops /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target ==>
  stmt_frag ctx func cx lctx
    (\v ee r. ?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
    ce (stmt_env ce lctx ret (Return (SOME e)))
    (eval_stmt cx (Return (SOME e))) es
Proof
  strip_tac >>
  `ce.ce_return_pc = NONE` by
    (drule_all return_selected_consumer_resources >> simp[]) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all return_consumer_compile_split >> strip_tac >>
  `ci_mono sa sb` by
    (qspecl_then [`ce`,`ret`,`e`,`sa`] mp_tac (cj 2 ci_mono_compile_expr_sa) >>
     simp[]) >>
  `!sx. ci_mono sx
    (SND (return_consumer_suffix ce ret (lowered_value_type ce e) op sx))` by
    (gen_tac >> pure_rewrite_tac[return_consumer_suffix_def] >>
     irule ci_mono_bind >> conj_tac
     >~ [`ce.ce_raw_return`]
     >- (rpt gen_tac >> BETA_TAC >> IF_CASES_TAC
         >- (irule ci_mono_ignore_bind >> conj_tac
             >- (gen_tac >> IF_CASES_TAC >>
                 simp[ci_mono_context_helpers, ci_mono_comp_return]) >>
             gen_tac >> irule ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >>
             rpt gen_tac >> BETA_TAC >> irule ci_mono_ignore_bind >>
             simp[ci_mono_typed_memory_family, ci_mono_return_helpers]) >>
         simp[ci_mono_return_helpers]) >>
     rpt gen_tac >> IF_CASES_TAC >> simp[ci_mono_comp_return] >>
     irule ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >>
     rpt gen_tac >> irule ci_mono_bind >> simp[ci_mono_comp_return] >>
     rpt gen_tac >> irule ci_mono_ignore_bind >>
     simp[ci_mono_typed_memory_family, ci_mono_comp_return]) >>
  `cs_extends sa sb /\ cs_extends sb cs'` by
    (qpat_x_assum `!sx. ci_mono _ _` (qspec_then `sb` mp_tac) >>
     simp[ci_mono_def] >> fs[ci_mono_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all return_prefix_code_resources >> strip_tac >>
  `expr_sim ctx func ce
      (initial_evaluation_context am.sources am.layouts tx NONE) ret e es /\
   expr_vv_sim ctx func ce
      (initial_evaluation_context am.sources am.layouts tx NONE) ret e es` by simp[] >>
  drule_all return_selected_forced_prefix >> strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ H _` >> strip_tac >>
  `(\res ee t. ?v. res = INL v /\ H (INL v) ee t) = H` by
    (simp[FUN_EQ_THM] >> rpt gen_tac >> Cases_on `res` >> simp[Abbr `H`]) >>
  irule return_counted_continuation >>
  qexists_tac `\v ee t. H (INL v) ee t` >>
  conj_tac
  >- (rpt gen_tac >> simp[Abbr `H`] >>
      disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      `expr_post ctx func ce
        (initial_evaluation_context am.sources am.layouts tx NONE) e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)
        sa sb s0 ee v op t` by simp[return_expr_post_start_gas_obs] >>
      qmatch_goalsub_abbrev_tac `stmt_exit RetQ` >>
      qsuff_tac `?n r. gas_path ctx func t n r /\ exit_result r /\ RetQ v ee r`
      >- (strip_tac >> qexistsl_tac [`n`,`r`] >> simp[] >>
          fs[stmt_exit_def, Abbr `RetQ`, return_result_gas_obs,
            return_result_scopes]) >>
      simp[Abbr `RetQ`] >> irule return_selected_success_suffix >> simp[] >>
      qpat_assum `expr_post _ _ _ _ _ (_ with gas_obs := _) _ _ _ _ _ _ _`
        (irule_at Any) >>
      qpat_assum `IS_SOME (type_stmt _ _ _)` (irule_at Any) >>
      qpat_assum `set_external_package_target _ _ = _` (irule_at Any) >>
      simp[] >>
      qpat_assum `lower_vyper_runtime_unit _ _ = _` (irule_at Any) >>
      qpat_assum `compile_register_positional_args _ _ _ _ = _` (irule_at Any) >>
      CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  BETA_TAC >> asm_rewrite_tac[]
QED

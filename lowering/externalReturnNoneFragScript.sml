(* Counted valueless return in a selected external frame. *)
Theory externalReturnNoneFrag
Ancestors externalReturnSimpleSuffix externalReturnValuedFrag
  externalReturnSelectedResources rawReturnHeader
  gasOutcome gasSummary gasSummaryCompose fragGasMode
  stmtSimDefs loweringPosts bodySim exprSimHypsDefs vyperTypeSystem
  vyperInterpreter vyperState vyperValueOperation compileEnv stmtLowering
  exprLoweringProps externalReturnCountedBoundary externalReturnPackage
  compileVyper entryStateRel

Theorem return_selected_none_frag:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops = SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops F nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return NONE)) /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\ cx.txn.target = tx.target ==>
  stmt_frag ctx func cx lctx
    (\v ee r. ?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
    ce (stmt_env ce lctx ret (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  strip_tac >>
  `ret = NoneT` by fs[type_stmt_def] >> gvs[] >>
  drule_all return_selected_consumer_resources >> strip_tac >>
  `~lookup_raw_return_or_F (NONE:num option) tx.function_name External tops` by
    (drule_all source_typing_none_return_plain >> simp[]) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `ce.ce_ctor_exit_label = NONE` by
    (drule return_package_target_inversion >> strip_tac >>
     drule compile_register_positional_args_cenv >> strip_tac >>
     fs[same_frame_def, compile_env_component_equality] >>
     qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
     simp[package_external_fn_def, update_cenv_nonreentrant_def,
       build_compile_env_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     simp[compile_env_component_equality] >> strip_tac >> gvs[]) >>
  `state_rel func ce cx es s0` by fs[stmt_state_rel_def] >>
  drule_all return_none_suffix_path >>
  disch_then (qspecl_then [`am.exports`,`ctx`] strip_assume_tac) >>
  simp[gas_outcome_def] >> qexists_tac `REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR (ReturnException NoneV)`, `es`, `r`] >>
  conj_tac
  >- (irule gas_marked_exec_no_source_read >>
      simp[Once evaluate_def, raise_def, gas_marked_path_def]) >>
  disj2_tac >> simp[stmt_exit_def, return_result_gas_obs, return_result_scopes,
    vyperValueTheory.evaluate_type_def, safe_cast_def]
QED

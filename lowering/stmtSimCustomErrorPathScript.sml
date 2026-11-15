(* Allocation/store/tail composition for custom-error statements. *)
Theory stmtSimCustomErrorPath
Ancestors
  stmtSimCustomErrorPrepare stmtSimCustomErrorGasPath exprSimSubscriptMap
  stmtSimCustomErrorSourcePath bodyCustomErrorExprReady bodyCustomErrorReady
  stmtSimCustomErrorStore stmtSimCustomErrorRevert abiEncoderProps
  exprLoweringProps loweringStateRelDefs loweringPosts exprSimHypsDefs compileEnv valueEncodingDefs
  fragGasPathMem venomMemDefs venomState finite_map pred_set
  stmtSimDefs bodyCustomErrorSource stmtSimLogAllocate stmtLowering
  abiEncoderAppend abiDecoderAppend externalEntryShape loweringSlice fragExec
  exprSimAggregatesAllocCounted allocLimits bodySim exprSimSource
  bodySimExprCases bodyCustomErrorWindowBounds supportedExprs vyperValue bodyExprPreFacts
  abiCallerTupleLayout valueEncodingProps list vyperTypeABI
  stmtSimDeclCompose gasSummaryCompose gasOutcome gasSummary gasContext gasCount
  gasExemptCert fragGasMode fragGasPath vyperInterpreter vyperState

Theorem custom_error_stored_tuple_revert_path:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env ee /\
  evaluate_type (get_tenv cx) (TupleT (MAP SND params)) = SOME (TupleTV tvs) /\
  value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
  vyper_to_abi (get_tenv cx) (TupleT (MAP SND params)) (ArrayV (TupleV vs)) = SOME av /\
  tuple_in_memory vs tvs b r.vs_memory /\ type_memory_size_list tvs <= asz /\
  not_fresh_at sm x /\ lookup_var x r = SOME (n2w b) /\
  FLOOKUP r.vs_allocas aid = SOME (b,asz) /\ aid < sm.cs_next_id /\
  custom_error_revert_tail ce id (MAP SND params) (Var x) no_args sm = ((),sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND params)) + 32 < 2 ** 64 /\
  stmt_state_rel ctx func ce cx ee r /\ ~r.vs_halted /\
  r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_path_mem ctx func r 0 (Abort Revert_abort t) /\
      abi_encoder_registered_effect (frag_ids sm sb) [] r t
Proof
  strip_tac >>
  `?at rv.
    abi_encoder_admissible
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND params))) /\
    eval_operand (Var x) r = SOME (n2w b) /\
    FLOOKUP r.vs_allocas aid = SOME (b,asz) /\
    type_memory_bytes ce (TupleT (MAP SND params)) <= asz /\
    abi_encoder_window_input
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND params)))
      at rv b (type_memory_bytes ce (TupleT (MAP SND params))) r.vs_memory /\
    enc at rv = enc (vyper_to_abi_type (get_tenv cx) (TupleT (MAP SND params))) av /\
    LENGTH (enc at rv) <= abi_size_bound ce.ce_struct_fields (TupleT (MAP SND params))` by
    (irule custom_error_store_encoder_endpoint >>
     conj_tac >- (qexistsl_tac [`r`,`sm`] >> simp[]) >>
     metis_tac[]) >>
  drule custom_error_revert_tail_run >>
  disch_then (qspecl_then [`ctx`,`func`] mp_tac) >>
  simp[] >> disch_then (qspecl_then [`r`,`b`,`aid`,`asz`,`at`,`rv`] mp_tac) >>
  simp[frag_ids_def] >>
  impl_tac >- (fs[stmt_state_rel_def] >> metis_tac[]) >> simp[]
QED

Theorem cs_appends_custom_error_revert_tail:
  cs_appends (custom_error_revert_tail ce id tys buf no_args)
Proof
  rewrite_tac[custom_error_revert_tail_def] >>
  irule cs_appends_bind >> simp[cs_appends_abi_alloc_buffer] >> gen_tac >>
  irule cs_appends_bind >> simp[cs_appends_return] >> gen_tac >>
  irule cs_appends_ignore_bind >> simp[cs_appends_emit_helpers] >>
  Cases_on `no_args` >> simp[]
  >- (irule cs_appends_bind >> simp[cs_appends_emit_helpers]) >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac >>
  irule cs_appends_bind >> simp[cj 2 cs_appends_abi_encode_mutual] >> gen_tac >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers] >> gen_tac >>
  irule cs_appends_bind >> simp[cs_appends_emit_helpers]
QED

Theorem compile_raise_custom_error_ready_frag:
  !cx err tops ctx func cenv env env' ret_ty lctx RetQ es.
    body_inv tops ctx cenv cx /\
    EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
    custom_error_resolved [(NONE,tops)] err /\
    (!target. supported_stmt_expr_exists
      (expr_abi_decode_target_root target) (Raise (RaiseCustomError err)) ==>
      occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
    stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty /\
    body_exprs_ok cx (custom_error_exprs err) ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
      (eval_stmt cx (Raise (RaiseCustomError err))) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `err` >>
  drule_all custom_error_body_resolution >> strip_tac >>
  `compile_revert_with_custom_error cenv (CustomError p l l0) sa = ((),sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     Cases_on `compile_revert_with_custom_error cenv (CustomError p l l0) sa` >>
     rename1 `_ = (u,last)` >> Cases_on `u` >> simp[] >> metis_tac[]) >>
  drule_all compile_revert_with_custom_error_split >> strip_tac >>
  `cs_extends sa sa'` by
    metis_tac[cs_appends_abi_alloc_buffer, cs_appends_def] >>
  `cs_extends sa' sm` by
    metis_tac[cj 1 compile_custom_error_labels, pairTheory.SND] >>
  `cs_extends sm sb` by
    metis_tac[cs_appends_custom_error_revert_tail, cs_appends_def] >>
  `cs_extends sa' sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sa' func /\ fn_has_code sa' sb func` by
    metis_tac[fn_has_code_split] >>
  `fn_has_code sa' sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) custom_error_allocate_store_ready >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `type_stmt _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `compile_custom_error_store_args _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  irule gas_outcome_zero_prefix >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >>
  drule_at (Pat `gas_outcome _ _ _ _ _ _ _`)
    (Q.INST [`RetQ` |-> `RetQ`] custom_error_args_revert_outcome) >>
  disch_then (drule_at (Pat `gas_admissible _ _ _`)) >>
  disch_then (drule_at (Pat `get_module_code _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_custom_error_args_in _ _ = _`)) >>
  disch_then (drule_at (Pat `order_custom_error_args _ _ = _`)) >>
  (impl_tac >- suspend "stored_tuple_tail") >>
  disch_then (qspec_then `\v ee r. F` (mp_then Any mp_tac gas_outcome_conseq)) >>
  simp[stmt_exit_def, exprSimDefsTheory.expr_exit_def] >>
  disch_then irule >> rpt strip_tac >> simp[]
QED

Resume compile_raise_custom_error_ready_frag[stored_tuple_tail]:
  rpt strip_tac >> gvs[] >>
    qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
    rewrite_tac[gas_marked_exec_def] >> strip_tac >>
    qpat_assum `!tail. eval_exprs _ _ _ = _`
      (qspec_then `[]` assume_tac) >>
    `expr_sim_inv cenv cx env
      (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
    qpat_x_assum `!tail. eval_exprs _ _ _ = _` kall_tac >>
    fs[APPEND_NIL] >>
    drule_at (Pat `eval_exprs _ _ _ = _`) custom_error_raise_source_ready >>
    disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
    disch_then (drule_at (Pat `type_stmt _ _ _ = _`)) >>
    fs[expr_sim_inv_gas_obs, vyperTypeCallGraphTheory.int_calls_stmt_def,
       vyperTypeCallGraphTheory.int_calls_raise_reason_def] >>
    strip_tac >> gvs[] >>
    `~r.vs_halted` by
      metis_tac[gas_marked_path_exec, gas_path_normal] >>
    `not_fresh_at sm x` by
      (irule loweringShapeDefsTheory.not_fresh_at_mono >>
       qexists_tac `sa'` >> simp[] >>
       mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_custom_error) >>
       disch_then (qspecl_then [`cenv`,`custom_error_exprs (CustomError p l l0)`,
         `MAP SND params`,`Var x`,`0`,`sa'`] mp_tac) >>
       simp[ci_mono_def]) >>
    drule_at (Pat `custom_error_revert_tail _ _ _ _ _ _ = _`)
      custom_error_stored_tuple_revert_path >>
    disch_then (drule_at (Pat `tuple_in_memory _ _ _ _`)) >>
    disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ mid r`)) >>
    disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
    disch_then (drule_at (Pat `expr_sim_inv _ _ _ mid`)) >>
    disch_then (qspecl_then [`av`,`type_memory_bytes cenv (TupleT (MAP SND params))`,
      `sa.cs_next_id`] mp_tac) >>
    simp[] >>
    (impl_tac >- (
      mp_tac (cj 1 stmtLoweringMonoTheory.ci_mono_custom_error) >>
      disch_then (qspecl_then [`cenv`,`custom_error_exprs (CustomError p l l0)`,
        `MAP SND params`,`Var x`,`0`,`sa'`] mp_tac) >>
      simp[ci_mono_def])) >> metis_tac[]
QED

Finalise compile_raise_custom_error_ready_frag

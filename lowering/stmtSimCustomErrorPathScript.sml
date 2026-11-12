(* Allocation/store/tail composition for custom-error statements. *)
Theory stmtSimCustomErrorPath
Ancestors
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


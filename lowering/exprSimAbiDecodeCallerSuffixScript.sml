Theory exprSimAbiDecodeCallerSuffix
Ancestors
  loweringStateRelDefs
  exprSimAbiDecodeCountedOutcome exprSimAbiDecodeBodySuccess
  exprSimAbiDecodeInputBound exprSimAbiDecodeReject exprSimAbiDecodeResources
  exprOperandVar exprReasonOperand exprSimAbiDecodeLiveFrame
  gasSummary exprSimHypsDefs localPtrsProps exprLoweringProps
  exprSimAbiDecodeOblivious exprSimAbiDecodeBodyEntry abiDecoderReentry
  compileEnv exprLowering exprSimAbiDecodeEntryTyping vyperTypeExprSoundness
  vyperTypeSystem exprSafeOperand exprSimHyps exprOpenFirstOperand

Theorem abi_decode_caller_suffix_summary:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\
  expr_post ctx func ce cx e es sa start s0 (ee with gas_obs := []) (BytesV bs) data s /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ local_ptrs_reserved ce sa /\
  lower_value compile_expr ce (expr_type e) e sa = (data,start) /\
  lower_abi_decode data
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (bind (lift_sum (evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs]))
      (\w. return (Value w))) (ee with gas_obs := [],s)
    (\res es1 t. ?v. res = INL (Value v) /\
      vv_post ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa final s0
        es1 (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts)
    (\res es1 r. expr_exit res r)
Proof
  strip_tac >>
  `cs_extends sa start` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends start final` by metis_tac[lower_abi_decode_frag_facts] >>
  `sa.cs_next_var <= start.cs_next_var /\ start.cs_next_var <= final.cs_next_var` by
    (conj_tac >- metis_tac[cj 2 compile_expr_grows] >>
     qpat_assum `lower_abi_decode _ _ _ _ _ _ = _`
       (mp_tac o Q.AP_TERM `SND`) >>
     metis_tac[ci_mono_lower_abi_decode, ci_mono_def, pairTheory.SND]) >>
  `local_ptrs_reserved ce start` by metis_tac[local_ptrs_reserved_next_var] >>
  `abi_size_bound ce.ce_struct_fields
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < dimword (:256)` by
    metis_tac[abi_decode_body_input_word_bound] >>
  `type_memory_bytes ce
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < dimword (:256)` by
    (drule abi_decode_body_output_bound >> simp[wordsTheory.dimword_def] >> decide_tac) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n))) /\
    ~is_word_type (expr_type e)` by
    (`well_typed_expr env e /\ env.type_defs = get_tenv cx` by
       metis_tac[expr_body_pre_def, abi_decode_parent_type, abi_decode_inv_type_env,
         listTheory.CONS_11] >>
     `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
       metis_tac[expr_body_pre_type_builtin_head, expr_body_pre_type_evaluates] >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), compileEnvTheory.is_word_type_def]) >>
  drule_all abi_decode_caller_resources >> strip_tac >>
  `abi_decoder_operand_live start.cs_next_var data` by
    (`!x. data = Var x ==> not_fresh_at start x` by
       metis_tac[compile_lower_value_var] >>
     Cases_on `data` >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def]) >>
  `data <> Label start.cs_current_bb` by
    (`expr_body_pre ce cx env e es` by metis_tac[expr_body_pre_type_builtin_head] >>
     irule lower_compile_expr_not_label >> goal_assum (drule_at Any) >>
     qexists_tac `env` >> fs[expr_body_pre_def, expr_sim_inv_def]) >>
  `immutable_alloca_sep func ce cx (ee with gas_obs := []) s` by
    (fs[loweringPostsTheory.expr_post_def, stmt_state_rel_def,
       immutable_alloca_sep_def, local_region_def] >> metis_tac[]) >>
  drule abi_decode_body_wrapped_coherent >> strip_tac >>
  `assignable_type (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)` by
    metis_tac[abi_decode_body_wrapped_assignable] >>
  `abi_decode_bytes_widths (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)` by
    metis_tac[abi_decode_body_wrapped_widths] >>
  `final.cs_next_var <= final.cs_next_var` by simp[] >>
  drule_all (Q.INST [`limit_st` |-> `final`] abi_decode_counted_outcome) >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- suspend "success" >>
  drule abi_decode_builtin_reject >> strip_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def,
    vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def,
    vyperStateTheory.return_def] >>
  qexistsl_tac [`INR (Error (RuntimeError e'))`, `ee`, `Abort Revert_abort u`] >>
  gvs[vyperStateTheory.raise_def, exprSimDefsTheory.expr_exit_def]
QED

Resume abi_decode_caller_suffix_summary[success]:
  `?rtv. evaluate_type (get_tenv cx) ty = SOME rtv` by
    (drule abi_decode_body_target >> strip_tac >>
     drule vyperTypeSystemTheory.assignable_type_well_formed >>
     simp[vyperTypeSystemTheory.well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `tv = (if unwrap /\ needs_external_call_wrap ty then TupleTV [rtv] else rtv)` by
    (drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
     fs[abiDecoderCoherenceTheory.abi_decoder_header_def] >>
     drule abi_decode_wrapped_type >> metis_tac[optionTheory.SOME_11]) >>
  gvs[] >>
  `?v. evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs] = INL v /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa final s0
      (ee with gas_obs := []) (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t` by
    (irule abi_decode_body_caller_success >> simp[] >>
     metis_tac[]) >>
  simp[gas_summary_at_def, gas_marked_exec_def,
    vyperStateTheory.bind_def, vyperStateTheory.lift_sum_def,
    vyperStateTheory.return_def] >>
  qexistsl_tac [`INL (Value v)`, `ee`, `OK t`] >>
  gvs[vyperStateTheory.return_def]
QED
Finalise abi_decode_caller_suffix_summary

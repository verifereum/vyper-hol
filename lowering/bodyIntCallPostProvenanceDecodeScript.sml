(* Decoder ownership stays attached to the decoder's successful endpoint. *)
Theory bodyIntCallPostProvenanceDecode
Ancestors
  bodyIntCallProducerInterface exprSimAbiDecode exprSimAbiDecodeCallerSuffix
  exprSimAbiDecodeOblivious exprSimSource exprSimAbiDecodeBodyEntry
  exprSimAbiDecodeInputBound exprOperandVar abiDecoderReentry exprSafeOperand exprOpenFirstOperand
  exprSimAbiDecodeEntryTyping exprSimAbiDecodeEntryLayout exprSimAbiDecodeEntryMetadata
  exprSimAbiDecodeRegionFrame exprSimAbiDecodeValueFrame
  exprSimAbiDecodeImmutableOutcome exprSimAbiDecodeQuantifiedLift
  exprSimAbiDecodeSetupExec exprSimProps loweringStateRelDefs
  exprSimHypsDefs exprSimHyps exprSimDefs exprLoweringProps loweringPosts
  gasOutcome gasSummary gasSummaryCompose vyperState vyperAST compileEnv
  exprLowering exprSimUnwrap fragExec

Theorem intcall_decode_success_provenance:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce dec_ty)
    (abi_static_size ce.ce_struct_fields dec_ty) (abi_size_bound ce.ce_struct_fields dec_ty)
    (type_memory_bytes ce dec_ty) start = (out,final) /\
  local_ptrs_reserved ce start /\
  (!i. MEM i (frag_code start final) ==> MEM i (fn_insts func)) /\
  alloca_inv s /\ fn_inst_ids_distinct func /\ local_ptrs_rel func ce es.scopes s /\
  abi_decode_success_closed ce (get_tenv cx) dec_ty dec_tv bs out d start final ctx func s t /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  type_memory_size tv <= type_memory_bytes ce dec_ty /\ sa.cs_next_id <= start.cs_next_id ==>
  intcall_vv_provenance ce cx ty sa final es (Value v)
    (LocatedValue ty (mk_ptr out LocMemory)) t
Proof
  strip_tac >>
  `val_footprint tv v <= type_memory_size tv` by simp[val_footprint_le] >>
  drule abi_decode_success_value >> strip_tac >>
  drule abi_decode_success_address_bound >> strip_tac >>
  drule abi_decode_output_site_interval >> strip_tac >>
  simp[intcall_vv_provenance_def, contextTheory.mk_ptr_def,
       read_result_def, return_def] >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  qexistsl_tac [`abi_builtin_decode_output_site start
      (abi_static_size ce.ce_struct_fields dec_ty) (abi_size_bound ce.ce_struct_fields dec_ty)`,
      `d`, `type_memory_bytes ce dec_ty`] >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >>
      `local_region ce es.scopes s n lb lsz` by
        metis_tac[exprSimAbiDecodeStateFrameTheory.abi_decode_success_local_region] >>
      drule_all abi_decode_success_output_local_disjoint >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  fs[abi_decode_success_closed_def] >> decide_tac
QED

Theorem intcall_decode_suffix_summary:
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
      t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
      intcall_vv_provenance ce cx ty sa final es1 (Value v)
        (LocatedValue ann (mk_ptr out LocMemory)) t)
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
    metis_tac[exprSimAbiDecodeInputBoundTheory.abi_decode_body_input_word_bound] >>
  `type_memory_bytes ce
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) < dimword (:256)` by
    (drule exprSimAbiDecodeBodyEntryTheory.abi_decode_body_output_bound >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic n))) /\
    ~is_word_type (expr_type e)` by
    (`well_typed_expr env e /\ env.type_defs = get_tenv cx` by
       metis_tac[expr_body_pre_def, exprSimAbiDecodeEntryTypingTheory.abi_decode_parent_type,
         exprSimAbiDecodeEntryTypingTheory.abi_decode_inv_type_env, listTheory.CONS_11] >>
     `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
       metis_tac[expr_body_pre_type_builtin_head, expr_body_pre_type_evaluates] >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(), compileEnvTheory.is_word_type_def]) >>
  drule_all exprSimAbiDecodeResourcesTheory.abi_decode_caller_resources >> strip_tac >>
  suspend "setup"
QED

Resume intcall_decode_suffix_summary[setup]:
  `abi_decoder_operand_live start.cs_next_var data` by
    (`!x. data = Var x ==> not_fresh_at start x` by
       metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
     Cases_on `data` >> gvs[abiDecoderReentryTheory.abi_decoder_operand_live_def,
       abiDecoderReentryTheory.abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `data <> Label start.cs_current_bb` by
    (`expr_body_pre ce cx env e es` by metis_tac[expr_body_pre_type_builtin_head] >>
     irule exprReasonOperandTheory.lower_compile_expr_not_label >> goal_assum (drule_at Any) >>
     qexists_tac `env` >> fs[expr_body_pre_def, expr_sim_inv_def]) >>
  `immutable_alloca_sep func ce cx (ee with gas_obs := []) s` by
    (fs[expr_post_def, stmt_state_rel_def, immutable_alloca_sep_def, local_region_def] >> metis_tac[]) >>
  drule exprSimAbiDecodeBodyEntryTheory.abi_decode_body_wrapped_coherent >> strip_tac >>
  `assignable_type (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)` by
    metis_tac[exprSimAbiDecodeBodyEntryTheory.abi_decode_body_wrapped_assignable] >>
  `abi_decode_bytes_widths (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty)` by
    metis_tac[exprSimAbiDecodeBodyEntryTheory.abi_decode_body_wrapped_widths] >>
  `final.cs_next_var <= final.cs_next_var` by simp[] >>
  drule_all (Q.INST [`limit_st` |-> `final`]
    exprSimAbiDecodeCountedOutcomeTheory.abi_decode_counted_outcome) >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- suspend "success" >>
  drule exprSimAbiDecodeRejectTheory.abi_decode_builtin_reject >> strip_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def, bind_def, lift_sum_def, return_def] >>
  qexistsl_tac [`INR (Error (RuntimeError e'))`, `ee`, `Abort Revert_abort u`] >>
  gvs[raise_def, expr_exit_def]
QED

Resume intcall_decode_suffix_summary[success]:
  `?rtv. evaluate_type (get_tenv cx) ty = SOME rtv` by
    (drule exprSimAbiDecodeBodyEntryTheory.abi_decode_body_target >> strip_tac >>
     drule vyperTypeSystemTheory.assignable_type_well_formed >>
     simp[vyperTypeSystemTheory.well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `tv = (if unwrap /\ needs_external_call_wrap ty then TupleTV [rtv] else rtv)` by
    (drule abiDecoderCoherenceTheory.abi_decoder_coherent_header >>
     fs[abiDecoderCoherenceTheory.abi_decoder_header_def] >>
     drule exprSimAbiDecodeEntryTypingTheory.abi_decode_wrapped_type >>
     metis_tac[optionTheory.SOME_11]) >>
  gvs[] >>
  `?v. evaluate_type_builtin cx (AbiDecode unwrap) ty [expr_type e] [BytesV bs] = INL v /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa final s0
      (ee with gas_obs := []) (Value v) (LocatedValue ann (mk_ptr out LocMemory)) t` by
    (irule exprSimAbiDecodeBodySuccessTheory.abi_decode_body_caller_success >> simp[] >>
     metis_tac[]) >>
  `intcall_vv_provenance ce cx ty sa final (ee with gas_obs := []) (Value v)
    (LocatedValue ann (mk_ptr out LocMemory)) t` by suspend "ownership" >>
  simp[gas_summary_at_def, gas_marked_exec_def, bind_def, lift_sum_def, return_def] >>
  qexistsl_tac [`INL (Value v)`, `ee`, `OK t`] >> gvs[return_def]
QED

Resume intcall_decode_suffix_summary[ownership]:
  `ann = ty` by
    metis_tac[exprSimAbiDecodeBodyEntryTheory.abi_decode_body_target] >>
  gvs[] >> rename1 `TypeBuiltin ty (AbiDecode unwrap) ty [e]` >>
  `val_wf rtv v` by
    fs[vv_post_def, vv_at_def, post_value_type_def, contextTheory.mk_ptr_def,
       expr_type_def, read_result_def, return_def] >>
  `type_memory_bytes ce ty = type_memory_size rtv` by
    (irule exprSimAbiDecodeEntryLayoutTheory.abi_decode_descended_memory_size >>
     qexistsl_tac [`get_tenv cx`, `get_tenv cx`] >> simp[] >>
     irule exprSimAbiDecodeEntryMetadataTheory.abi_decode_root_metadata_inv >>
     qexistsl_tac [`env`, `es`] >> fs[expr_body_pre_def]) >>
  `sa.cs_next_id <= start.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `alloca_inv s /\ local_ptrs_rel func ce (ee with gas_obs := []).scopes s` by
    fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `abi_decode_immutable_success _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_decode_immutable_success_def] >> strip_tac >>
  irule intcall_decode_success_provenance >>
  goal_assum (drule_at (Pat `abi_decode_success_closed _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  fs[abiDecodeUnwrapCaseTheory.abi_decode_output_size] >>
  qexists_tac `data` >> simp[] >>
  metis_tac[exprSimAbiDecodeResourcesTheory.abi_decode_resources_code_member]
QED
Finalise intcall_decode_suffix_summary

Theorem intcall_decode_normal_prefix_summary:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es /\
  expr_type e = BaseT (BytesT (Dynamic n)) /\ local_ptrs_reserved ce sa /\
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
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK s) /\
  expr_post ctx func ce cx e es sa start s0 (ee with gas_obs := []) v data s /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts ==>
  gas_summary_at F (ctx,func) marks
    (eval_expr cx (TypeBuiltin ann (AbiDecode unwrap) ty [e])) (es,s0)
    (\res es1 t. ?tv. res = INL tv /\
      vv_post ctx func ce cx (TypeBuiltin ann (AbiDecode unwrap) ty [e]) es sa final s0
        es1 tv (LocatedValue ann (mk_ptr out LocMemory)) t /\
      t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts /\
      intcall_vv_provenance ce cx ty sa final es1 tv
        (LocatedValue ann (mk_ptr out LocMemory)) t)
    (\res es1 r. expr_exit res r)
Proof
  strip_tac >>
  `expr_body_pre ce cx env e es` by metis_tac[expr_body_pre_type_builtin_head] >>
  `evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic n)))` by
    (drule expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v, ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
      (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_result_typed env e (Value v)` by
    (irule (cj 3 expr_body_pre_eval) >>
     qexistsl_tac [`ce`, `cx`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `ee with gas_obs := []`] >> fs[bind_def]) >>
  `?bs. v = BytesV bs` by
    (`env.type_defs = get_tenv cx` by
       metis_tac[abi_decode_inv_type_env, expr_body_pre_def] >>
     fs[vyperTypeExprResultTheory.expr_result_typed_def,
        vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
        vyperTypeInvariantsTheory.value_result_typed_def] >>
     Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >> gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule exprSimAbiDecodeBodySuccessTheory.abi_decode_observed_scopes_dom >> simp[]) >>
  `lower_value compile_expr ce (expr_type e) e sa = (data,start)` by metis_tac[] >>
  drule_all intcall_decode_suffix_summary >>
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  `ann = ty` by metis_tac[abi_decode_parent_type, expr_body_pre_def] >>
  pop_assum SUBST_ALL_TAC >>
  rewrite_tac[exprSimAbiDecodeBodySuccessTheory.abi_decode_singleton_source] >>
  qexistsl_tac [`res`, `es_end`, `r`] >>
  (conj_tac
   >- (irule (SRULE [] (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal)) >>
       goal_assum (drule_at Any) >> metis_tac[]) >>
   gvs[] >> metis_tac[])
QED

Theorem intcall_abi_decode_outcome:
  exprs_case F ctx func cenv cx args /\
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es /\
  compile_expr cenv (expr_type (TypeBuiltin ann (AbiDecode unwrap) ty args))
    (TypeBuiltin ann (AbiDecode unwrap) ty args) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx (TypeBuiltin ann (AbiDecode unwrap) ty args)) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (eval_expr cx (TypeBuiltin ann (AbiDecode unwrap) ty args)) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (TypeBuiltin ann (AbiDecode unwrap) ty args)
        es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance cenv cx (expr_type (TypeBuiltin ann (AbiDecode unwrap) ty args))
        sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `well_typed_expr env (TypeBuiltin ann (AbiDecode unwrap) ty args)` by
    fs[expr_body_pre_def] >>
  drule abi_decode_parent_type >> strip_tac >> gvs[exprs_case_def] >>
  `expr_body_pre cenv cx env e es` by metis_tac[expr_body_pre_type_builtin_head] >>
  `expr_sim ctx func cenv cx (expr_type e) e es` by
    (qpat_x_assum `expr_sim_case _ _ _ _ _ _`
      (irule o REWRITE_RULE [expr_sim_case_def]) >>
     metis_tac[exprSimHypsTheory.int_calls_type_builtin_arg, listTheory.MEM]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_type_builtin_dispatch,
       Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[oneline exprLoweringTheory.as_ptr_val_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `compile_expr cenv (BaseT (BytesT (Dynamic n))) e sa = (evv, sm)` >>
  rename1 `unwrap_value cenv evv sm = (data, start)` >>
  `lower_value compile_expr cenv (expr_type e) e sa = (data,start)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa start` by
    metis_tac[compile_expr_extends, unwrap_value_extends, cs_extends_trans] >>
  drule lower_abi_decode_frag_facts >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `start`, `data`, `s0`] mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "summary" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule exprSimAbiDecodeComposeTheory.abi_decode_child_exempt_cert >> simp[]
QED

Resume intcall_abi_decode_outcome[summary]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >> strip_tac
  >- (gvs[] >>
      `~t.vs_halted` by
        metis_tac[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_exec,
          fragGasPathTheory.gas_path_normal] >>
      simp[expr_type_def] >>
      irule intcall_decode_normal_prefix_summary >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  Cases_on `res` >- gvs[expr_exit_def] >>
  irule exprSimAbiDecodeComposeTheory.abi_decode_child_exit_summary >>
  qexistsl_tac [`es_end`, `y`, `r`] >> simp[] >>
  Cases_on `y` >> Cases_on `r` >> gvs[expr_exit_def] >>
  Cases_on `e'` >> gvs[expr_exit_def]
QED
Finalise intcall_abi_decode_outcome

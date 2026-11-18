Theory bodyFullAbiEncodeNonwordFull
Ancestors
  bodyFullPreds bodySimFull bodyInvNoDalloca bodyFullAbiEncodeArgStep
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish bodyFullAbiEncodeAllocOrigin
  bodyFullAbiEncodeSuffix bodyFullAbiEncodeUniformTranslation
  exprSimAbiEncodeNonwordCase exprSimAbiEncodeRuntimeInputs
  exprSimAbiEncodeNonwordResources exprSimAbiEncodeCapacity
  exprSimAbiEncodeNonwordResult bodyFullAbiEncodeReadResources
  exprSimIfExpWidenedPhysicalType bodyFullAbiEncodeNonwordWindow
  abiEncodeMaterialize valueCopyBytes bodyFullAbiEncodeSetupSourceFrame
  exprSimHyps exprSimSource gasOutcomeFullCompose gasShadowCompile
  gasShadowCompileStmtHelpers exprLowering compileEnv

Theorem abi_encode_nonword_vv_full_from_packaging:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  body_expr_full_ok cx e /\ ~is_word_type (expr_type e)
  ==> expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr ce cty (TypeBuiltin ann _ _ _) sa = _` mp_tac >>
  simp[compile_abi_encode_nonword_shape] >>
  pairarg_tac >> rename1 `lower_value _ _ _ _ sa = (op,sm)` >>
  simp[] >> simp[as_ptr_val_def] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) op
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) sm` >>
  rename1 `lower_abi_encode _ _ _ _ _ sm = (out,sn)` >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `lower_value _ _ _ e sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >>
  rename1 `compile_expr ce (expr_type e) e sa = (vv,si)` >>
  strip_tac >> gvs[] >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`]
    gas_shadow_stmt_compile_expr) >>
  rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  gvs[] >> rename1 `gas_shadow_state si shadow_si` >>
  rename1 `compile_expr ce (expr_type e) e sa = (vv,si)` >>
  mp_tac (Q.INST [`cenv` |-> `ce`] gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value) >>
  rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`si`,`shadow_si`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `unwrap_value ce vv shadow_si` >> gvs[] >>
  rename1 `gas_shadow_state sm shadow_sm` >>
  qpat_x_assum `compile_expr ce cty (gas_shadow_expr _) shadow_sa = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def, compile_abi_encode_nonword_shape,
    gasShadowTheory.gas_shadow_expr_type,
    lower_value_def, comp_bind_def, as_ptr_val_def] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) op
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) shadow_sm` >>
  simp[as_ptr_val_def, contextTheory.mk_ptr_def] >> strip_tac >> gvs[] >>
  rename1 `fn_has_code shadow_sa shadow_sb shadow_func` >>
  `cs_extends sa si /\ cs_extends shadow_sa shadow_si` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `cs_extends si sm /\ cs_extends shadow_si shadow_sm` by
    metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[cs_extends_trans] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    metis_tac[abiBuiltinEncodeWordTheory.lower_abi_encode_extends] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  mp_tac (Q.INST [`rest` |-> `[]`, `mid` |-> `si`, `sb` |-> `sm`,
    `shadow_mid` |-> `shadow_si`, `shadow_sb` |-> `shadow_sm`]
    abi_encode_arg_step_full) >>
  simp[expr_can_mutate_def] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  simp[eval_expr_singleton_type_builtin_action,
    vyperContextTheory.type_builtin_args_length_ok_def] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
      vyperStorageTraceTheory.evaluate_storage_trace_frame,
      vyperStorageTraceTheory.storage_trace_frame_read_result]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_def]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_value >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
      first_assum ACCEPT_TAC) >>
  qexists `childQ` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      simp[Abbr `childR`] >> rpt strip_tac >>
      Cases_on `res` >- gvs[exprSimDefsTheory.expr_exit_def] >>
      qexists `y` >> Cases_on `r` >> Cases_on `y` >>
      gvs[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >>
      gvs[exprSimDefsTheory.expr_exit_def]) >>
  map_every qx_gen_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> childQ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac bool_ss [Abbr `childQ`] >> strip_tac >> gvs[] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[post_value_type_nonword] >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME ptv` by
    metis_tac[post_type_evaluates] >>
  `~is_word_type (lowered_value_type ce e)` by
    metis_tac[expr_body_pre_lowered_fits,
      exprSimLayoutTransportTheory.compatible_word_type] >>
  `expr_post (storage_trace_horizon ee.storage_trace)
    ctx func ce cx e es sa sm s0 ee v op s` by metis_tac[] >>
  `~is_word_type (post_value_type ce e) ==> !w.
     eval_operand op s = SOME w ==>
     type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= s.vs_alloca_next` by
    metis_tac[arithmeticTheory.ADD_COMM] >>
  drule_all abi_encode_arg_positive_resources >> simp[] >> strip_tac >>
  `value_runtime_typed env (post_value_type ce e) v` by
    (irule memory_rhs_read_post_typed >>
     qexistsl_tac [`cx`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
       `ee with gas_obs := []`] >> simp[] >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[ETA_THM, exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def] >>
     metis_tac[memory_rhs_read_post_typed]) >>
  `value_has_type ptv v` by
    (gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
       exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `val_footprint tv v = val_footprint ptv v` by
    (drule expr_body_pre_lowered_fits >> strip_tac >>
     drule_all materialize_post_lowered_classify >> strip_tac
     >- gvs[] >>
     metis_tac[bytestring_val_footprint_eq]) >>
  `?w. eval_operand op s = SOME w` by
    gvs[loweringPostsTheory.expr_val_rel_def] >>
  `op_taint tn1 op = {}` by gvs[bodyPtrDefsTheory.ptr_val_ok_def] >>
  `!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
      val_in_memory ptv v (w2n w) mem` by
    (gvs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def] >>
     metis_tac[]) >>
  `!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem` by
    (drule expr_body_pre_lowered_fits >> strip_tac >>
     drule_all materialize_post_lowered_classify >> strip_tac >- gvs[] >>
     rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
     conj_tac >- simp[] >>
     qexistsl_tac [`post_value_type ce e`, `lowered_value_type ce e`,
       `get_tenv cx`, `ptv`] >> simp[]) >>
  `?av. vyper_to_abi (get_tenv cx) (lowered_value_type ce e) v = SOME av` by
    metis_tac[cj 1 vyperTypeABITheory.vyper_to_abi_total] >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx)` by
    fs[exprSimHypsDefsTheory.expr_body_pre_def,
       exprSimHypsDefsTheory.expr_sim_inv_def] >>
  `!t v. evaluate_type (get_tenv cx) t = SOME v ==>
      type_memory_bytes ce t = type_memory_size v` by
    metis_tac[exprSimAbiEncodeSourceMetadataTheory.abi_encode_body_evaluated_metadata] >>
  `?ct rv. enc ct rv = enc (vyper_to_abi_type (get_tenv cx)
       (lowered_value_type ce e)) av /\
    !mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
      abi_encoder_window_input
        (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
        ct rv (w2n w) (val_footprint tv v) mem` by
    (irule abi_encode_uniform_translated_footprint_window >>
     simp[] >> qexists_tac `get_tenv cx` >> simp[]) >>
  `?stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
      value_has_type stv v` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >> drule_at (Pat `bind _ _ _ = _`)
       (CONV_RULE (DEPTH_CONV ETA_CONV)
         exprSimAbiEncodePrefixWindowTheory.abi_encode_operand_success_type) >>
     disch_then (qspecl_then [`env`, `ce`] mp_tac) >> simp[]) >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits] >>
  `vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
   vyper_to_abi_type (get_tenv cx) (lowered_value_type ce e) =
     vyper_to_abi_type (get_tenv cx) (expr_type e)` by
    metis_tac[exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_conversion,
      exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_abi_type] >>
  drule_all abi_encode_nonword_numerical_capacity >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `lower_abi_encode _ _ _ _ _ sm = _`
    (strip_assume_tac o MATCH_MP abiBuiltinEncodeCodeTheory.lower_abi_encode_trace) >>
  drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_trace >> strip_tac >>
  `cs_extends sm ready` by
    (drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_shape >>
     strip_tac >> irule cs_extends_same_block >> simp[]) >>
  `cs_extends ready body_end` by
    metis_tac[loweringHaltTheory.compile_abi_encode_to_buf_extends] >>
  `cs_extends body_end sb` by
    (drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_finish_shape >>
     strip_tac >> irule cs_extends_same_block >> simp[]) >>
  `cs_extends sm allocated` by
    metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends allocated address_st` by
    metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape] >>
  `cs_extends address_st ready` by
    (qpat_x_assum `abi_builtin_encode_method_id _ _ _ = _` mp_tac >>
     Cases_on `mid`
     >- simp[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def,
          comp_return_def, cs_extends_refl] >>
     simp[abiBuiltinEncodeCodeTheory.abi_builtin_encode_method_id_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_var_def, fresh_id_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_def] >> strip_tac >> gvs[] >>
     simp[cs_extends_def, GSYM listTheory.APPEND_ASSOC,
       rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sm ready func /\ fn_has_code ready body_end func /\
   fn_has_code body_end sb func /\ fn_has_code sm allocated func /\
   fn_has_code allocated ready func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `local_ptrs_reserved ce sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[] >>
     qpat_assum `compile_expr ce (expr_type e) e sa = _`
       (strip_assume_tac o MATCH_MP exprSimUnwrapTheory.compile_expr_extends) >>
     mp_tac (Q.SPECL [`ce`,`vv`,`si`] exprLoweringPropsTheory.ci_mono_unwrap_value) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >> strip_tac >> decide_tac) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace)
      ctx func ce cx ee s` by fs[loweringPostsTheory.expr_post_def] >>
  `ghost_inv_at (DF (storage_trace_horizon ee.storage_trace))
      lo d ce cx ee G1 tn1 s` by metis_tac[] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_footprint_le,
      cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `0 < val_footprint ptv v ==>
     w2n w + val_footprint ptv v <= s.vs_alloca_next` by
    (strip_tac >>
     `0 < type_memory_size tv` by decide_tac >>
     qpat_assum `~is_word_type (post_value_type ce e) ==> !w. _`
       (drule o Q.SPEC `w` o UNDISCH) >> strip_tac >> decide_tac) >>
  `32 + 32 * word_size
      (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) +
       (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))
      < dimword (:256)` by (Cases_on `mid` >> fs[]) >>
  drule_all abi_encode_nonword_setup_output >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `alloca_inv (abi_builtin_allocate_state _ outsz s)` >>
  qmatch_asmsub_abbrev_tac `alloca_inv alloc_model` >>
  drule_all abi_encode_alloc_origin_exact >>
  disch_then (qspecl_then [`tn1`, `gas_explicit_sites ctx shadow_ctx`, `PG`, `G1`] mp_tac) >>
  strip_tac >>
  rename1 `lookup_var q allocated_s = SOME outw` >>
  rename1 `ptr_covers G2 tn2 q allocated_s outsz` >>
  `allocated_s.vs_allocas = alloc_model.vs_allocas /\
   allocated_s.vs_alloca_next = alloc_model.vs_alloca_next` by simp[Abbr `alloc_model`] >>
  `p = w2n outw` by
    (qpat_assum `FLOOKUP allocated_s.vs_allocas _ = _` mp_tac >>
     qpat_assum `allocated_s.vs_allocas = alloc_model.vs_allocas`
       (fn th => pure_rewrite_tac [th]) >>
     strip_tac >> gvs[]) >>
  `alloca_inv allocated_s /\ alloca_room ctx func allocated_s` by
    metis_tac[localPtrsPropsTheory.alloca_inv_fields,
      exprLoweringPropsTheory.alloca_room_fields] >>
  `~allocated_s.vs_halted` by
    (qpat_assum `allocated_s with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_halted`) >> simp[]) >>
  `lo <= w2n outw` by
    (qpat_assum `allocas_from lo allocated_s`
       (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
     disch_then (qspecl_then [`sm.cs_next_id`, `w2n outw`, `outsz`] mp_tac) >>
     simp[]) >>
  `lookup_var q allocated_s = SOME (n2w (w2n outw))` by simp[] >>
  qpat_assum `buf.buf_operand = Var q` (fn th =>
    rule_assum_tac (REWRITE_RULE [th])) >>
  drule_at (Pat `emit_op _ _ _ = _`) abi_encode_setup_tail_origin >>
  disch_then (drule_at (Pat `abi_builtin_encode_method_id _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ptr_covers G2 tn2 q allocated_s outsz`)) >>
  disch_then (drule_at (Pat `fn_has_code allocated ready func`)) >>
  disch_then (drule_at (Pat `allocas_from lo allocated_s`)) >>
  simp[Abbr `outsz`] >>
  disch_then (qspec_then `w2n outw` mp_tac) >>
  disch_then (qspec_then `abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)` mp_tac) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `ctx`, `PG`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> strip_tac >>
  rename1 `ptr_covers setupG setupTN dp setup_s _` >>
  `allocated_s.vs_memory = s.vs_memory` by
    (qpat_assum `allocated_s with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s`
       (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >> simp[]) >>
  `val_wf tv v` by metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `!mem. mem_agree_outside tn2.t_mem allocated_s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem` by
    (rpt strip_tac >>
     irule ghostObservationPtrTheory.robust_val_in_memory_exterior_no_new_taint >>
     simp[] >>
     qexistsl_tac [`{i | s.vs_alloca_next <= i}`, `s.vs_memory`,
       `allocated_s.vs_memory`, `tn1.t_mem`, `tn2.t_mem`] >>
     simp[] >> (metis_tac[])) >>
  `setupTN.t_mem SUBSET tn2.t_mem` by
    (qpat_assum `setupTN.t_mem = _` (fn th => rewrite_tac[th]) >>
     simp[pred_setTheory.DIFF_SUBSET]) >>
  `32 + (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 32)
      <= outsz` by
    (Cases_on `mid` >> simp[Abbr `outsz`] >>
     mp_tac (Q.SPEC `abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)+4`
       exprSimPropsTheory.le_word_size_mul) >> intLib.COOPER_TAC) >>
  `!mem. mem_agree_outside setupTN.t_mem setup_s.vs_memory mem ==>
      val_in_memory tv v (w2n w) mem` by
    (irule abi_encode_setup_source_robust >>
     qexistsl [`allocated`, `w2n outw`, `outsz`,
       `case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 32`,
       `allocated_s`, `tn2`] >> simp[] >>
     metis_tac[]) >>
  FAIL_TAC "setup window"
QED

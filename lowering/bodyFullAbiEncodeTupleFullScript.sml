(* The non-fast-path AbiEncode branch uses one tuple and one physical suffix. *)
Theory bodyFullAbiEncodeTupleFull
Ancestors
  bodyFullPreds bodySimFull bodyInvNoDalloca
  bodyFullAbiEncodeArgs bodyFullAbiEncodeTupleAlloc bodyFullAbiEncodeTupleZero
  bodyFullAbiEncodeUniformTranslation bodyFullAbiEncodeSuffix
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish
  exprSimAbiEncodeTupleCase exprSimAbiEncodeRuntimeInputs
  exprSimAbiEncodeTupleResources exprSimAbiEncodeSourceMetadata
  exprSimAbiEncodeOblivious abiBuiltinAllocation abiTupleEncodePrepare fragExec
  emitHelper context
  exprSimHyps exprSimHypsDefs exprSimSource abiEncodeArgsCase abiEncodeArgsSim
  vyperTypeSystem
  gasOutcomeFullCompose gasShadowCompile gasShadowCompileHelpers gasShadowState
  gasShadowCompileConvert exprLoweringProps exprLowering exprCallBounds compileEnv emitHelperProps
  vyperEvalExprPreservesScopesDom vyperInterpreter vyperState vyperAST vyperContext
  list arithmetic words

Theorem tuple_compile_shape[local]:
  ~(LENGTH args = 1 /\ ~ensure) ==>
  compile_expr ce cty (TypeBuiltin ann (AbiEncode ensure mid) target args) sa =
    let (ops,st) = compile_abi_encode_args compile_expr ce args sa in
    let (buf,allocated) = compile_alloc_buffer
      (type_memory_bytes ce (TupleT (MAP (lowered_value_type ce) args))) st in
    let (_,staged) = compile_store_abi_tuple ce buf.buf_operand 0
      (ZIP (ops,MAP (lowered_value_type ce) args)) allocated in
    as_ptr_val ann LocMemory
      (lower_abi_encode ensure (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
        (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
        (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) staged)
Proof
  strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[expr_size_def, list_size_def, expr_type_def, comp_bind_def] >>
  AP_TERM_TAC >> AP_THM_TAC >>
  irule compile_abi_encode_args_callback_cong >>
  rpt strip_tac >> simp[FUN_EQ_THM] >> rpt gen_tac >>
  simp[expr_list_member_bound]
QED

Theorem tuple_source_action[local]:
  1 <= LENGTH args ==>
  eval_expr cx (TypeBuiltin ann (AbiEncode ensure mid) target args) =
  bind (eval_exprs cx args)
    (\vs es. ((case evaluate_type_builtin cx (AbiEncode ensure mid) target
      (MAP expr_type args) vs of
      INL w => INL (Value w) | INR err => INR (Error err)),es))
Proof
  strip_tac >> rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, type_check_def, type_builtin_args_length_ok_def,
    assert_def, ignore_bind_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx args x` >> Cases_on `q` >>
  simp[lift_sum_def, bind_def, return_def, raise_def] >>
  rename1 `eval_exprs cx args x = (INL vs,ee)` >>
  Cases_on `evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs` >>
  simp[bind_def, return_def, raise_def]
QED

Theorem tuple_compiled_layout[local]:
  ~(LENGTH args = 1 /\ ~ensure) /\
  compile_expr ce cty (TypeBuiltin ann (AbiEncode ensure mid) ty args) sa = (vv,sf) /\
  fn_has_code sa sf func ==>
  ?ops st buf allocated staged out.
    compile_abi_encode_args compile_expr ce args sa = (ops,st) /\
    compile_alloc_buffer (type_memory_bytes ce (TupleT (MAP (lowered_value_type ce) args))) st =
      (buf,allocated) /\
    compile_store_abi_tuple ce buf.buf_operand 0
      (ZIP (ops,MAP (lowered_value_type ce) args)) allocated = ((),staged) /\
    lower_abi_encode ensure (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
      (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
      (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) staged =
      (out,sf) /\ vv = LocatedValue ann (mk_ptr out LocMemory) /\
    cs_extends sa st /\ cs_extends st staged /\ cs_extends staged sf /\
    fn_has_code sa st func /\ fn_has_code st sf func
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  dep_rewrite.DEP_REWRITE_TAC [tuple_compile_shape] >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  Cases_on `lower_abi_encode ensure (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
    (abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args))) staged` >>
  gvs[as_ptr_val_def] >>
  rename1 `lower_abi_encode _ _ _ _ _ staged = (out,sf)` >>
  `ci_mono sa st` by metis_tac[abi_args_compile_mono, pairTheory.SND] >>
  `cs_extends sa st` by fs[ci_mono_def] >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  `cs_extends st staged` by (irule cs_extends_same_block >> simp[]) >>
  `!l. buf.buf_operand <> Label l` by
    (qpat_x_assum `emit_op ALLOCA _ st = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     Cases_on `buf.buf_operand` >> gvs[]) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  `cs_extends st sf` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split]
QED

Theorem abi_encode_tuple_vv_full_from_packaging:
  !tops ctx ce cx env ann ensure mid ty args es DF lo d shadow_ctx PG func shadow_func cty.
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
  ~(LENGTH args = 1 /\ ~ensure) /\
  (!s'' x t. type_check
      (type_builtin_args_length_ok (AbiEncode ensure mid) (LENGTH args))
      "TypeBuiltin args" s'' = (INL x,t) ==> body_exprs_full_ok cx args) ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx cty (TypeBuiltin ann (AbiEncode ensure mid) ty args) es
Proof
  rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `1 <= LENGTH args` by
    (fs[expr_body_pre_def, well_typed_expr_def, well_typed_type_builtin_args_def,
        type_builtin_args_length_ok_def] >> Cases_on `args` >> gvs[]) >>
  `body_exprs_full_ok cx args` by
    (qpat_x_assum `!s'' x t. _` (qspecl_then [`es`, `()`, `es`] mp_tac) >>
     simp[type_check_def, type_builtin_args_length_ok_def, assert_def, return_def]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all tuple_compiled_layout >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_expr ce cty (gas_shadow_expr _) shadow_sa = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def] >> strip_tac >>
  drule_at (Pat `compile_expr _ _ _ shadow_sa = _`) tuple_compiled_layout >>
  simp[] >> disch_then drule_all >> strip_tac >>
  rename1 `compile_abi_encode_args compile_expr ce (MAP gas_shadow_expr args) shadow_sa =
    (shadow_ops,shadow_st)` >>
  `gas_shadow_compiles (compile_abi_encode_args compile_expr ce args)
     (compile_abi_encode_args compile_expr ce (MAP gas_shadow_expr args))` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `sh` |-> `T`]
      (MATCH_MP gas_shadow_compiles_abi_encode_args (cj 1 gas_shadow_compile_expr))) >> simp[]) >>
  qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
  rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  `!q gs. expr_sim_inv ce cx env q ==> expr_sim_inv ce cx env (q with gas_obs := gs)`
    by simp[] >>
  `EVERY (\e. !q. expr_sim_inv ce cx env q ==> expr_body_pre ce cx env e q) args` by
    (simp[EVERY_MEM] >> metis_tac[abi_args_body_pre_arg]) >>
  `EVERY (\e. !q v q'. expr_sim_inv ce cx env q /\
    bind (eval_expr cx e) (read_result cx) q = (INL v,q') ==>
    expr_sim_inv ce cx env q' /\ MAP FDOM q'.scopes = MAP FDOM q.scopes) args` by
    (fs[EVERY_MEM] >> metis_tac[abi_args_success_ready]) >>
  drule_all (SRULE [] (Q.INST [`Inv` |-> `expr_sim_inv ce cx env`]
    (SPEC_ALL abi_encode_args_full))) >>
  disch_then (qspec_then `PG` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ argsQ argsR` >>
  dep_rewrite.DEP_REWRITE_TAC [tuple_source_action] >> simp[] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (next v)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_def]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_results >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_results >>
      first_assum ACCEPT_TAC) >>
  qexists `argsQ` >> reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      simp[Abbr `argsR`] >> rpt strip_tac >>
      Cases_on `res` >> gvs[exprSimWordArgsTheory.wb_args_exit_def] >> metis_tac[]) >>
  FAIL_TAC "tuple continuation"
QED

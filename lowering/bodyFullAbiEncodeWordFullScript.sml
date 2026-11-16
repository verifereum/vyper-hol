Theory bodyFullAbiEncodeWordFull
Ancestors
  bodySimFull bodyInvNoDalloca bodyFullAbiEncodeAllocOrigin
  bodyFullAbiEncodeStore bodyFullAbiEncodeSuffix bodyFullAbiEncodeUniformTranslation
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish gasShadowCompile
  exprSimSource exprSimHyps gasExemptCert gasShadowCompileStmtHelpers
  exprSimAbiEncodeWordCase exprSimAbiEncodeRuntimeInputs
  gasOutcomeFullCompose exprLowering compileEnv vyperContext vyperState
  exprLoweringProps exprBopSimProps exprBopLowering abiBuiltinAllocation abiBuiltinEncodeWord
  emitHelper vyperAST list loweringPosts exprSimAbiEncodeOblivious fragExec

Theorem abi_encode_word_compile_shape[local]:
  is_word_type (expr_type e) ==>
  compile_expr ce cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) sa =
    let (op,sm) = lower_value compile_expr ce (expr_type e) e sa in
    let (buf,sn) = compile_alloc_buffer 32 sm in
    let (_,sh) = emit_void MSTORE [buf.buf_operand;op] sn in
    as_ptr_val ann LocMemory
      (lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
        (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
        (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) sh)
Proof
  strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, expr_size_def, list_size_def, expr_type_def,
       comp_bind_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem abi_encode_word_vv_full_from_packaging:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es /\ is_word_type (expr_type e)
  ==> expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `compile_expr ce cty (TypeBuiltin _ _ _ _) sa = _` mp_tac >>
  simp[abi_encode_word_compile_shape] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) sh` >>
  rename1 `lower_abi_encode _ _ _ _ _ sh = (out,final)` >>
  gvs[as_ptr_val_def] >>
  `cs_extends sa sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends sm sh` by
    (drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
     irule cs_extends_same_block >> simp[]) >>
  `!l. buf.buf_operand <> Label l` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     qpat_x_assum `emit_op ALLOCA _ sm = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     Cases_on `buf.buf_operand` >> gvs[]) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split, cs_extends_trans] >>
  Cases_on `lower_value compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) shadow_sa = (shop,shadow_sm)` >>
  `shop = op /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`]
      gas_shadow_stmt_lower_value) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[]) >> gvs[] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr (TypeBuiltin _ _ _ _)) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def, abi_encode_word_compile_shape] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) buf'.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) sh'` >>
  gvs[as_ptr_val_def, contextTheory.mk_ptr_def] >>
  rename1 `lower_abi_encode _ _ buf'.buf_operand _ _ sh' = (out,shadow_sb)` >>
  `cs_extends shadow_sa shadow_sm` by metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends shadow_sm sh'` by
    (drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
     irule cs_extends_same_block >> simp[]) >>
  `!l. buf'.buf_operand <> Label l` by
    (drule_at (Pat `compile_alloc_buffer _ shadow_sm = _`)
       abi_builtin_alloc_buffer_shape >> strip_tac >>
     qpat_x_assum `emit_op ALLOCA _ shadow_sm = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     Cases_on `buf'.buf_operand` >> gvs[]) >>
  `cs_extends sh' shadow_sb` by metis_tac[lower_abi_encode_frag_facts] >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  simp[expr_sim_full_def] >> disch_then drule_all >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  FAIL_TAC "child outcome obtained"
QED

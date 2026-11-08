Theory exprSimAbiEncodeWordCase
Ancestors
  exprSimAbiEncodeWordResult exprSimAbiEncodeNonwordCase exprSimAbiEncodeNonwordResult
  exprSimAbiEncodeRuntimeInputs exprSimAbiEncodePrefixWindow
  exprSimHash exprSimHypsDefs exprSimDefs exprLowering exprBopLowering
  fragExec exprSimSource vyperTypeABI
  exprLoweringProps exprBopSimProps abiBuiltinAllocation abiBuiltinEncodeWord
  compileEnv emitHelper vyperAST vyperState vyperContext vyperInterpreter
  list vyperTypeCallGraph loweringPosts exprOperandVar
  exprSimAbiEncodeOblivious vyperTypeInvariants vyperEvalExprPreservesScopesDom

Theorem compile_abi_encode_word_shape[local]:
  is_word_type (expr_type e) ==>
  compile_expr ce cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) sa =
    let (op,sm) = lower_value compile_expr ce (expr_type e) e sa in
    let (buf,sn) = compile_alloc_buffer 32 sm in
    let (_,sh) = emit_void MSTORE [buf.buf_operand;op] sn in
    as_ptr_val ann LocMemory
      (lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
        (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
        (abi_size_bound ce.ce_struct_fields (expr_type e)) sh)
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

Theorem compile_abi_encode_word_vv_sim:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_sim ctx func ce cx (expr_type e) e es /\
  is_word_type (expr_type e) ==>
  expr_vv_sim ctx func ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_def] >> rpt strip_tac >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_abi_encode_word_shape] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  suspend "compose"
QED

Resume compile_abi_encode_word_vv_sim[compose]:
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
    (abi_size_bound ce.ce_struct_fields (expr_type e)) sh` >>
  rename1 `lower_abi_encode _ _ _ _ _ sh = (out,final)` >>
  gvs[as_ptr_val_def] >>
  `abi_size_bound ce.ce_struct_fields (expr_type e) = 32` by
    metis_tac[abi_encode_word_size_bound] >>
  `!l. buf.buf_operand <> Label l` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     qpat_x_assum `emit_op ALLOCA _ sm = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
       fresh_id_def, emit_def, comp_return_def] >> strip_tac >> gvs[] >> Cases_on `buf.buf_operand` >> gvs[]) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule abi_builtin_encode_word_stage_shape >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `cs_extends sm sh` by (irule cs_extends_same_block >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sh func /\ fn_has_code sh final func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible] >>
  `eval_expr cx (TypeBuiltin ann (AbiEncode F mid) ty [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. ((case evaluate_type_builtin cx (AbiEncode F mid) ty [expr_type e] [v] of
        INL w => INL (Value w) | INR err => INR (Error err)),ee))` by
    (irule eval_expr_singleton_type_builtin_action >>
     simp[type_builtin_args_length_ok_def]) >>
  asm_rewrite_tac[] >> irule expr_sim_suffix >>
  first_assum (irule_at (Pat `expr_sim _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> Cases_on `exc` >> Cases_on `r` >> simp[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  rpt strip_tac >> suspend "success"
QED

Resume compile_abi_encode_word_vv_sim[success]:
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) abi_encode_operand_success_type) >>
  disch_then (qspecl_then [`env`,`ce`] mp_tac) >> simp[] >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at sm x` by metis_tac[compile_lower_value_var] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     drule eval_expr_preserves_scopes_dom >> strip_tac >>
     drule read_result_state >> strip_tac >> gvs[]) >>
  drule_all abi_encode_nonword_source_result >> strip_tac >>
  `?actual. gas_marked_path F ctx func t 0 (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid) ty [e])
      es sa final s0 ee (Value (BytesV (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue (expr_type (TypeBuiltin ann (AbiEncode F mid) ty [e]))
        <|ptr_operand := out; ptr_location := LocMemory|>) actual` by
    (irule abi_encode_word_counted_success >>
     simp[] >> conj_tac >- (qexists `env` >> simp[]) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     gvs[]) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qexists `[]` >> simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl [`INL (Value (BytesV (abi_encode_method_id_bytes mid ++
    enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))`,
    `ee`, `OK actual`] >>
  simp[gasSummaryTheory.gas_marked_exec_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_type_def] >>
  mp_tac (GEN_ALL (Q.INST
    [`p` |-> `<|ptr_operand := out; ptr_location := LocMemory|>`,
     `q` |-> `mk_ptr out LocMemory`] abi_encode_vv_post_pointer_cong)) >>
  simp[contextTheory.mk_ptr_def] >>
  disch_then (fn th => rewrite_tac[GSYM th])
QED

Finalise compile_abi_encode_word_vv_sim

Theory exprSimAbiEncodeNonwordCase
Ancestors
  exprSimAbiEncodeNonwordResult abiBuiltinEncodeCode emitHelper compileEnv
  exprSimHash vyperInterpreter vyperState exprSimSource exprSimWordArgs
  exprLowering exprBopLowering vyperAST list exprSimHypsDefs exprSimDefs
  exprSimAbiEncodeRuntimeInputs vyperTypeCallGraph abiBuiltinEncodeWord
  exprLoweringProps exprBopSimProps vyperTypeSystem fragExec vyperContext
  exprSimAbiEncodePrefixWindow exprSimAbiEncodePlanTranslation vyperTypeABI
  exprOperandVar loweringPosts exprSimAbiEncodeTranslatedResult
  exprReasonOperand exprSimAbiEncodeOblivious vyperTypeInvariants
  vyperEvalExprPreservesScopesDom

Theorem abi_encode_endpoint_nonempty:
  lower_abi_encode ensure mid src info maxlen sa = (out,sb) ==>
  sb.cs_current_insts <> []
Proof
  strip_tac >> drule lower_abi_encode_trace >> strip_tac >>
  qpat_x_assum `abi_builtin_encode_finish _ _ _ _ = _` mp_tac >>
  simp[abi_builtin_encode_finish_def] >>
  IF_CASES_TAC >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem eval_expr_singleton_type_builtin_cases:
  type_builtin_args_length_ok tb 1 /\
  eval_expr cx (TypeBuiltin ann tb ty [e]) es = (res,es') ==>
  (?exc. bind (eval_expr cx e) (read_result cx) es = (INR exc,es') /\
         res = INR exc) \/
  ?v. bind (eval_expr cx e) (read_result cx) es = (INL v,es') /\
    res = (case evaluate_type_builtin cx tb ty [expr_type e] [v] of
             INL w => INL (Value w) | INR err => INR (Error err))
Proof
  strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx [e] es` >>
  rename1 `eval_exprs cx [e] es = (rr,es1)` >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[eval_exprs_nil] >>
  simp[bind_def, return_def, lift_sum_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs()] >>
  Cases_on `evaluate_type_builtin cx tb ty [expr_type e] [v]` >>
  gvs[return_def, raise_def] >> metis_tac[]
QED

Theorem eval_expr_singleton_type_builtin_action:
  type_builtin_args_length_ok tb 1 ==>
  eval_expr cx (TypeBuiltin ann tb ty [e]) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v es. ((case evaluate_type_builtin cx tb ty [expr_type e] [v] of
                INL w => INL (Value w) | INR err => INR (Error err)), es))
Proof
  strip_tac >> pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
  Cases_on `eval_expr cx (TypeBuiltin ann tb ty [e]) x` >>
  drule_all eval_expr_singleton_type_builtin_cases >> strip_tac >>
  gvs[bind_def]
QED

Theorem compile_abi_encode_nonword_shape:
  ~is_word_type (expr_type e) ==>
  compile_expr ce cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) sa =
    let (op,sm) = lower_value compile_expr ce (expr_type e) e sa in
    as_ptr_val ann LocMemory
      (lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) op
        (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
        (abi_size_bound ce.ce_struct_fields (expr_type e)) sm)
Proof
  strip_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[lower_value_child_call, expr_size_def, list_size_def, expr_type_def,
       lower_value_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[])
QED


Theorem abi_encode_vv_post_pointer_cong:
  p.ptr_operand = q.ptr_operand /\ p.ptr_location = q.ptr_location ==>
  (vv_post ctx func ce cx e es sa sb s0 es' tv (LocatedValue ty p) s <=>
   vv_post ctx func ce cx e es sa sb s0 es' tv (LocatedValue ty q) s)
Proof
  simp[vv_post_def, vv_holds_def, vv_at_def]
QED

Theorem abi_encode_translated_success_mk_ptr[local]:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  expr_body_pre ce cx env e es /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid0) ty [e]) es /\
  mid = OPTION_MAP bytes_method_id_word mid0 /\
  ~is_word_type (expr_type e) /\
  ei = type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  lower_abi_encode F mid op ei (abi_size_bound ce.ce_struct_fields (expr_type e)) sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!l. op <> Label l) /\ (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
   !bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  local_ptrs_reserved ce origin /\ origin.cs_next_var <= sa.cs_next_var /\
  origin.cs_next_id <= sa.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  ?actual.
    gas_marked_path F ctx func s 0 (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid0) ty [e])
      es origin sb s0 es'
      (Value (BytesV (abi_encode_method_id_bytes mid0 ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue ann (mk_ptr out LocMemory)) actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_translated_success_suffix >> strip_tac >>
  qexists_tac `actual` >> simp[] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_type_def, contextTheory.mk_ptr_def] >>
  mp_tac (GEN_ALL (Q.INST
    [`p` |-> `<|ptr_operand := out; ptr_location := LocMemory|>`,
     `q` |-> `mk_ptr out LocMemory`] abi_encode_vv_post_pointer_cong)) >>
  simp[contextTheory.mk_ptr_def] >>
  disch_then (fn th => rewrite_tac[GSYM th])
QED

Theorem compile_abi_encode_nonword_vv_sim:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  expr_sim ctx func ce cx (expr_type e) e es /\
  ~is_word_type (expr_type e) ==>
  expr_vv_sim ctx func ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >> rewrite_tac[expr_vv_sim_def] >> rpt strip_tac >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_abi_encode_nonword_shape] >>
  pairarg_tac >> rename1 `lower_value _ _ _ _ sa = (op,sm)` >>
  simp[] >> simp[as_ptr_val_def] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) op
    (type_to_abi_enc_info ce.ce_struct_fields ce (expr_type e))
    (abi_size_bound ce.ce_struct_fields (expr_type e)) sm` >>
  rename1 `lower_abi_encode _ _ _ _ _ sm = (out,sn)` >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  `!l. op <> Label l` by
    (irule lower_compile_expr_not_label >> goal_assum (drule_at Any) >>
     qexists_tac `env` >>
     fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def]) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `eval_expr cx (TypeBuiltin ann (AbiEncode F mid) ty [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. ((case evaluate_type_builtin cx (AbiEncode F mid) ty [expr_type e] [v] of
        INL w => INL (Value w) | INR err => INR (Error err)),ee))` by
    (irule eval_expr_singleton_type_builtin_action >>
     simp[type_builtin_args_length_ok_def]) >>
  asm_rewrite_tac[] >>
  irule expr_sim_suffix >>
  first_assum (irule_at (Pat `expr_sim _ _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> Cases_on `exc` >> Cases_on `r` >> simp[expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]) >>
  rpt strip_tac >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`)
    (CONV_RULE (DEPTH_CONV ETA_CONV) abi_encode_operand_success_type) >>
  disch_then (qspecl_then [`env`,`ce`] mp_tac) >> simp[] >> strip_tac >>
  drule_all (cj 1 vyper_to_abi_total) >> strip_tac >>
  drule_all abi_encode_nonword_source_result >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    metis_tac[compile_lower_value_var] >>
  `sb.cs_current_insts <> []` by metis_tac[abi_encode_endpoint_nonempty] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     drule eval_expr_preserves_scopes_dom >> strip_tac >>
     drule read_result_state >> strip_tac >> gvs[]) >>
  `?actual. gas_marked_path F ctx func t 0 (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = sb.cs_current_bb /\
    actual.vs_inst_idx = LENGTH sb.cs_current_insts /\
    vv_post ctx func ce cx (TypeBuiltin ann (AbiEncode F mid) ty [e])
      es sa sb s0 ee (Value (BytesV (abi_encode_method_id_bytes mid ++
        enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))
      (LocatedValue ann (mk_ptr out LocMemory)) actual` by
    (irule abi_encode_translated_success_mk_ptr >>
     simp[] >> conj_tac
     >- (qexists_tac `env` >> simp[]) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> qexists_tac `tv` >> simp[]) >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  qexists_tac `[]` >> simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INL (Value (BytesV (abi_encode_method_id_bytes mid ++
    enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av)))`,
    `ee`, `OK actual`] >>
  simp[gasSummaryTheory.gas_marked_exec_def]
QED

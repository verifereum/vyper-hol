Theory exprSimAbiEncodeNonwordCase
Ancestors
  exprSimAbiEncodeNonwordResult abiBuiltinEncodeCode emitHelper compileEnv
  exprSimHash vyperInterpreter vyperState exprSimSource exprSimWordArgs
  exprLowering exprBopLowering vyperAST list exprSimHypsDefs exprSimDefs
  exprSimAbiEncodeRuntimeInputs vyperTypeCallGraph abiBuiltinEncodeWord
  exprLoweringProps exprBopSimProps vyperTypeSystem fragExec vyperContext
  exprSimAbiEncodePrefixWindow exprSimAbiEncodePlanTranslation vyperTypeABI
  exprOperandVar loweringPosts

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


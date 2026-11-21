Theory exprSimAbiEncodeRuntimeInputs
Ancestors
  exprSimSource exprSimHyps exprSimHypsDefs exprSimDefs exprLowering exprCallBounds
  vyperInterpreter vyperState vyperContext
  context builtinAbi exprLoweringProps fragExec exprReasonOperand vyperTypeArgFits
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeSystem supportedExprTraverse supportedProgram vyperAST vyperTypeCallGraph
  compileEnv allocLimits list pair abiEncodeArgsCase exprSimAbiEncodeSourceMetadata
  exprSimAbiEncodeArgsPhysicalCapacity

Theorem compile_expr_abi_encode:
  compile_expr ce cty (TypeBuiltin ann (AbiEncode ensure mid) target args) sa =
    (\(vs,st). as_ptr_val ann LocMemory
       (lower_abi_encode (OPTION_MAP bytes_method_id_word mid)
         (abi_size_bound ce.ce_struct_fields
           (if LENGTH args = 1 /\ ~ensure then HD (MAP (lowered_value_type ce) args)
            else TupleT (MAP (lowered_value_type ce) args)))
         (compile_abi_encode_payload ce (LENGTH args = 1 /\ ~ensure) vs
           (MAP (lowered_value_type ce) args)) st))
      (compile_abi_encode_args compile_expr ce args sa)
Proof
  simp[compile_expr_type_builtin_dispatch,
       Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  AP_TERM_TAC >> AP_THM_TAC >>
  irule compile_abi_encode_args_callback_cong >>
  rpt strip_tac >> simp[FUN_EQ_THM, expr_child_callback_def] >> rpt gen_tac >>
  drule expr_list_member_bound >> simp[]
QED

Theorem compile_abi_encode_body_layout:
  compile_expr ce cty (TypeBuiltin ann (AbiEncode ensure mid) target args) sa =
    (vv,sf) /\ fn_has_code sa sf func ==>
  ?vs st out.
    compile_abi_encode_args compile_expr ce args sa = (vs,st) /\
    lower_abi_encode (OPTION_MAP bytes_method_id_word mid)
      (abi_size_bound ce.ce_struct_fields
        (if LENGTH args = 1 /\ ~ensure then lowered_value_type ce (HD args)
         else TupleT (MAP (lowered_value_type ce) args)))
      (compile_abi_encode_payload ce (LENGTH args = 1 /\ ~ensure) vs
        (MAP (lowered_value_type ce) args)) st = (out,sf) /\
    vv = LocatedValue ann (mk_ptr out LocMemory) /\
    LENGTH vs = LENGTH args /\ ci_mono sa st /\ ci_mono st sf /\
    fn_has_code sa st func /\ fn_has_code st sf func
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_abi_encode, LET_THM] >>
  pairarg_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `as_ptr_val ann LocMemory action` >>
  Cases_on `action` >> simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  rename1 `lower_abi_encode _ _ _ st = (out,sf)` >>
  `ci_mono sa st` by
    metis_tac[ci_mono_compile_abi_encode_args, cj 1 compile_expr_ci_mono, SND] >>
  `ci_mono st sf` by
    metis_tac[ci_mono_lower_abi_encode, ci_mono_compile_abi_encode_payload, SND] >>
  `fn_has_code sa st func /\ fn_has_code st sf func` by
    metis_tac[ci_mono_def, fn_has_code_split] >>
  qexists_tac `out` >> simp[] >>
  conj_tac >- (Cases_on `args` >> fs[]) >>
  metis_tac[compile_abi_encode_args_length, FST]
QED

Theorem compile_abi_encode_word_snapshot:
  lowered_value_type ce e = expr_type e /\ is_word_type (expr_type e) /\
  reason_result_shape (expr_type e) loc (FST (compile_expr ce (expr_type e) e sa)) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) ==>
  compile_abi_encode_args compile_expr ce [e] sa = ([StackValue (expr_type e) op],sm)
Proof
  strip_tac >>
  Cases_on `compile_expr ce (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sx)` >>
  Cases_on `vv` >>
  gvs[reason_result_shape_def, lower_value_def, compile_abi_encode_args_def,
      compile_ext_call_args_def, compile_snapshot_vv_def, ext_call_arg_value_def,
      unwrap_value_def, vv_type_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[vv_type_def, comp_bind_def, comp_return_def]) >> metis_tac[]
QED

Theorem compile_abi_encode_word_direct:
  lowered_value_type ce e = expr_type e /\ is_word_type (expr_type e) /\
  reason_result_shape (expr_type e) loc (FST (compile_expr ce (expr_type e) e sa)) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) ==>
  compile_expr ce cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) sa =
    as_ptr_val ann LocMemory
      (lower_abi_encode (OPTION_MAP bytes_method_id_word mid)
        (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e))
        (\dst. comp_ignore_bind (emit_void MSTORE [dst;op]) (comp_return (Lit 32w))) sm)
Proof
  strip_tac >> drule_all compile_abi_encode_word_snapshot >> strip_tac >>
  `compile_abi_encode_payload ce T [StackValue (expr_type e) op] [expr_type e] =
      (\dst. comp_ignore_bind (emit_void MSTORE [dst;op]) (comp_return (Lit 32w)))` by
    simp[FUN_EQ_THM, compile_abi_encode_payload_def, comp_bind_def,
         comp_return_def, unwrap_value_def, LET_THM] >>
  simp[compile_expr_abi_encode, LET_THM]
QED

Theorem eval_expr_abi_encode_action:
  1 <= LENGTH args ==>
  eval_expr cx (TypeBuiltin ann (AbiEncode ensure mid) target args) =
  bind (eval_exprs cx args)
    (\vs es. ((case evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs of
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

Theorem abi_encode_body_arg_pre:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  MEM arg args ==> expr_body_pre ce cx env arg es
Proof
  metis_tac[abi_args_body_pre_arg, expr_body_pre_def]
QED

Theorem abi_encode_eval_exprs_runtime_typed:
  well_typed_exprs env args /\ runtime_consistent env cx es /\
  functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs args) /\
  eval_exprs cx args es = (INL vs,es') ==>
  exprs_runtime_typed env args vs
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 1 (SPEC_ALL (cj 6 eval_scc_type_sound_mutual))) >> simp[]
QED

Theorem abi_encode_body_args_runtime_typed:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') ==>
  exprs_runtime_typed env args vs /\ env.type_defs = get_tenv cx
Proof
  strip_tac >>
  `well_typed_exprs env args /\ runtime_consistent env cx es /\
   functions_well_typed cx /\ call_evaluation_safe cx (int_calls_exprs args)` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def,
        runtime_consistent_def, int_calls_expr_def] >>
  `env.type_defs = get_tenv cx` by
    gvs[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  drule_all abi_encode_eval_exprs_runtime_typed >> simp[]
QED

Theorem abi_encode_body_args_indexed_types:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') ==>
  LENGTH args = LENGTH vs /\
  !k. k < LENGTH args ==> ?tv.
    evaluate_type (get_tenv cx) (expr_type (EL k args)) = SOME tv /\
    value_has_type tv (EL k vs)
Proof
  strip_tac >> drule_all abi_encode_body_args_runtime_typed >>
  simp[exprs_runtime_typed_def, LIST_REL_EL_EQN] >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem abi_encode_body_arg_copy_bound:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') /\ k < LENGTH args /\
  ~is_word_type (expr_type (EL k args)) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type (EL k args)) = SOME tv /\
    value_has_type tv (EL k vs) /\
    type_memory_bytes ce (expr_type (EL k args)) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64
Proof
  strip_tac >> drule_all abi_encode_body_args_indexed_types >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `expr_body_pre ce cx env (EL k args) es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[EL_MEM]) >>
  drule_all expr_body_pre_copy_ok >> metis_tac[]
QED

Theorem abi_encode_body_args_indexed_physical_types:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') ==>
  LENGTH args = LENGTH vs /\
  !k. k < LENGTH args ==> ?tv.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL k args)) = SOME tv /\
    value_has_type tv (EL k vs)
Proof
  strip_tac >>
  `EVERY (\e. expr_body_pre ce cx env e es) args` by
    (simp[EVERY_MEM] >> metis_tac[abi_encode_body_arg_pre]) >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type ce e) v) args vs` by
    (irule eval_exprs_physical_runtime_typed >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[memory_rhs_read_lowered_typed_unwidened]) >>
  drule_all abi_encode_body_args_runtime_typed >> strip_tac >>
  gvs[LIST_REL_EL_EQN, value_runtime_typed_def]
QED

Theorem abi_encode_body_arg_physical_copy_bound:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') /\ k < LENGTH args /\
  ~is_word_type (expr_type (EL k args)) ==>
  ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce (EL k args)) = SOME tv /\
    value_has_type tv (EL k vs) /\
    type_memory_bytes ce (lowered_value_type ce (EL k args)) = type_memory_size tv /\
    type_memory_size tv < 2 ** 64
Proof
  strip_tac >>
  drule_all abi_encode_body_args_indexed_physical_types >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `expr_body_pre ce cx env (EL k args) es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[EL_MEM]) >>
  drule_all abi_encode_body_evaluated_metadata >> strip_tac >>
  drule_all abi_encode_body_arg_copy_bound >> strip_tac >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  drule (cj 1 abi_args_fits_memory_bytes) >>
  disch_then (qspec_then `ce` assume_tac) >>
  qexists `tv` >> gvs[]
QED

Theorem abi_encode_body_args_physical_conversion:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  eval_exprs cx args es = (INL vs,es') ==>
  !k. k < LENGTH args ==>
    vyper_to_abi_type (get_tenv cx) (lowered_value_type ce (EL k args)) =
      vyper_to_abi_type (get_tenv cx) (expr_type (EL k args)) /\
    !v. vyper_to_abi (get_tenv cx) (lowered_value_type ce (EL k args)) v =
      vyper_to_abi (get_tenv cx) (expr_type (EL k args)) v
Proof
  strip_tac >> gen_tac >> strip_tac >>
  `expr_body_pre ce cx env (EL k args) es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[EL_MEM]) >>
  drule expr_body_pre_physical_type >> strip_tac >>
  drule_all abi_encode_body_args_indexed_types >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac
  >- (irule (cj 1 abi_args_fits_abi_type) >> simp[]) >>
  irule (cj 1 abi_args_fits_conversion) >> metis_tac[]
QED

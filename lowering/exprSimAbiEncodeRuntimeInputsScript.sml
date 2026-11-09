Theory exprSimAbiEncodeRuntimeInputs
Ancestors
  exprSimSource exprSimHyps exprSimHypsDefs exprSimDefs
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeSystem supportedExprTraverse supportedProgram vyperAST vyperTypeCallGraph
  compileEnv allocLimits list abiEncodeArgsCase exprSimAbiEncodeSourceMetadata
  exprSimAbiEncodeArgsPhysicalCapacity

Theorem abi_encode_body_arg_pre:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  MEM arg args ==> expr_body_pre ce cx env arg es
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
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

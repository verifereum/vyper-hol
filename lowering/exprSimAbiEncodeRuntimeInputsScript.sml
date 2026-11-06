Theory exprSimAbiEncodeRuntimeInputs
Ancestors
  exprSimSource exprSimHyps exprSimHypsDefs exprSimDefs
  vyperTypeEvalSoundness vyperTypeExprSoundness vyperTypeInvariants
  vyperTypeSystem supportedExprTraverse supportedProgram vyperAST vyperTypeCallGraph
  compileEnv allocLimits list

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

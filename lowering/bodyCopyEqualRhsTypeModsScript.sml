(* Physical types of RHS values whose lowering retains the annotation. *)
Theory bodyCopyEqualRhsTypeMods
Ancestors
  exprSimHypsDefs exprBodyPreProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeEvalSoundness vyperTypeInvariants vyperTypeExprSoundness
  typedMemoryCopy loweringPosts exprPtrUnwrapStorageShape

Theorem copy_equal_rhs_type_mods:
  expr_body_pre_mods mods ce cx env e es /\
  vyperState$bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  lowered_value_type ce e = expr_type e ==>
  ?rt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
       value_has_type rt v /\
       post_value_type ce e = lowered_value_type ce e /\
       type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt
Proof
  strip_tac >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  fs[runtime_consistent_def] >>
  drule_at (Pat `vyperState$bind _ _ _ = _`)
    (REWRITE_RULE [ETA_AX] eval_expr_read_type_sound) >>
  disch_then (qspec_then `env` mp_tac) >> simp[] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  fs[value_runtime_typed_def] >>
  simp[post_value_type_lowered] >>
  irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >> simp[] >>
  drule_then mp_tac expr_body_pre_mods_inv >>
  simp[expr_sim_inv_mods_def] >> metis_tac[]
QED

Theorem copy_nonmemory_rhs_type_mods:
  expr_body_pre_mods mods ce cx env e es /\
  vyperState$bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  compile_expr ce (expr_type e) e a = (LocatedValue ty p,sm) /\
  p.ptr_location <> LocMemory ==>
  ?rt. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
       value_has_type rt v /\
       post_value_type ce e = lowered_value_type ce e /\
       type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt
Proof
  strip_tac >>
  drule_all_then assume_tac compile_nonmemory_lowered_value_type >>
  irule copy_equal_rhs_type_mods >> simp[] >>
  qexistsl_tac [`ee`,`env`,`es`,`mods`] >> simp[]
QED

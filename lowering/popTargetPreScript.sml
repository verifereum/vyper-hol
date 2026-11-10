(*
 * A pop's target: target_pre, which target_case needs, from the pop's
 * expr_body_pre.
 *
 * TOP-LEVEL:
 *   target_pre_of_pop       — target_pre from a pop's expr_body_pre
 *)

Theory popTargetPre
Ancestors
  targetPlaceSim targetPlaceSimCasesBase exprSimHypsDefs
  vyperAST vyperTypeSystem vyperTypeEnv vyperTypeCallGraph
  vyperTypeCallStackSoundness supportedExprTraverse supportedProgram
  allocLimits list

(* Every index of a typed target meets expr_body_pre wherever expr_sim_inv
   holds, from the target's part of an expression's expr_body_pre. *)
Theorem target_indices_pre_of_body:
  !bt vt cenv cx env.
    type_place_target env bt = SOME vt /\ byte_widths_target bt /\
    alloc_limits_target cenv bt /\
    call_evaluation_safe cx (int_calls_target bt) /\
    ~supported_target_exists expr_evm_run_root bt /\
    ~supported_target_exists call_operands_effect_root bt /\
    EVERY (\c. FST c = NONE /\
               ?tops. supported_program tops /\
                      get_module_code cx NONE = SOME tops /\
                      IS_SOME (supported_function_decl tops c Internal))
          (int_calls_target bt) /\
    (!target. supported_target_exists (expr_abi_decode_target_root target) bt ==>
              occurs_abi_decode_target target (cx_tops cx)) /\
    (!target. is_dynamic (vyper_to_abi_type (get_tenv cx) target) ==>
              is_dynamic (vyper_to_abi_type (type_env (cx_tops cx)) target)) ==>
    target_indices_pre cenv cx env bt
Proof
  recInduct base_assignment_target_induct >> rw[target_indices_pre_def] >>
  gvs[type_place_target_AttributeTarget, type_place_target_SubscriptTarget,
      byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
      supported_expr_exists_def] >>
  imp_res_tac call_evaluation_safe_append_left >>
  imp_res_tac call_evaluation_safe_append_right
  >~ [`expr_body_pre _ _ _ e _`]
  >- rw[expr_body_pre_def, expr_has_evm_run_def] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* A pop's target meets target_pre where the pop meets expr_body_pre and
   its root is not an immutable. *)
Theorem target_pre_of_pop:
  !cenv cx env ann bt es.
    expr_body_pre cenv cx env (Pop ann bt) es /\ ~immutable_root cx bt ==>
    target_pre cenv cx env bt es
Proof
  rw[expr_body_pre_def, target_pre_def] >>
  gvs[Once well_typed_expr_def, byte_widths_expr_def, alloc_limits_expr_def,
      int_calls_expr_def, expr_has_evm_run_def, supported_expr_exists_def,
      expr_abi_decode_target_root_def, expr_evm_run_root_def,
      call_operands_effect_root_def] >>
  irule target_indices_pre_of_body >> simp[] >> metis_tac[]
QED

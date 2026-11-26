(* Linked typing of the unbound Raw operand result at a chosen observation. *)
Theory createSizeRawEvalTypingMods
Ancestors
  createCtorSnapshotTypingMods exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeSoundness vyperTypeExprSoundness

Theorem create_raw_eval_typing_at_obs_mods:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (res,ee) ==>
  no_type_error_result res /\
  (case res of INL tv => eval_result_typed (env,cx,ee) tv (Type (expr_type e))
             | INR _ => T)
Proof
  strip_tac >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by
    simp[ctor_snapshot_gas_pre_mods] >>
  qpat_x_assum `expr_body_pre_mods mods ce cx env e es` kall_tac >>
  drule expr_body_pre_mods_call_evaluation_safe >> strip_tac >>
  drule (REWRITE_RULE [runtime_consistent_def]
    expr_body_pre_mods_runtime_typing) >> strip_tac >>
  drule_all typed_expr_evaluation_sound >> simp[]
QED


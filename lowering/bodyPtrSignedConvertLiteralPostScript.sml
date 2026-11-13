Theory bodyPtrSignedConvertLiteralPost
Ancestors wordArgsPtr
  loweringPosts exprSimProps exprSimWordArgs exprLoweringProps
  bodyPtrDefs ptrDiscipline venomState

Theorem expr_post_initial_literal:
  !ctx func cenv cx e es s v w sa gs.
    is_word_type (expr_type e) /\
    stmt_state_rel ctx func cenv cx es s /\
    (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
          typed_val_to_w256 tv v = w) ==>
    expr_post ctx func cenv cx e es sa sa s (es with gas_obs := gs) v (Lit w) s
Proof
  rpt strip_tac >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, eval_operand_def]
QED

Theorem ptr_val_ok_word_literal:
  !cx t v w G tn s.
    is_word_type t ==> ptr_val_ok cx t v (Lit w) G tn s
Proof
  simp[ptr_val_ok_def, op_taint_def]
QED

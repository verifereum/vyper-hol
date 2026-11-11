(* Syntactic operand probes for the assignment frame interface. *)
Theory assignPlaceOperandFacts
Ancestors
  exprReasonOperand exprSimHypsDefs exprLowering compileEnv

Theorem assign_place_stack_operand_not_label:
  expr_body_pre cenv cx env e es /\
  compile_expr cenv (expr_type e) e sa = (StackValue rt op,sm) ==>
  !l. op <> Label l
Proof
  strip_tac >>
  `lower_value compile_expr cenv (expr_type e) e sa = (op,sm)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  irule lower_compile_expr_not_label >>
  goal_assum (drule_at Any) >>
  qexists_tac `env` >>
  gvs[expr_body_pre_def, expr_sim_inv_def]
QED

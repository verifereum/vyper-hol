(* Named constants forward the execution of the fresh value they wrap. *)
Theory bodyFullNamedConst
Ancestors
  bodyFullPreds bodyFullOfVV namedConstLoweredType bodyFullExprGeneric
  exprSimSource exprSimConvert exprBodyPreProps exprSimProps exprLoweringProps
  gasShadowCompile gasOutcomeFullCompose exprSimMemDefs exprSafeOperandBuiltins
  exprLowering loweringPosts vyperTypeSystem vyperContext vyperState vyperInterpreter

Theorem named_const_operand_eval_value[local]:
  named_const_operand e /\ eval_expr cx e st = (INL r,st') ==>
  ?v. r = Value v
Proof
  Cases_on `e` >> simp[oneline named_const_operand_def] >>
  metis_tac[eval_expr_literal_value, eval_expr_builtin_value,
            eval_expr_type_builtin_value]
QED

Theorem named_const_eval[local]:
  named_const_operand e ==>
  eval_expr cx (Builtin ann NamedConst [e]) = eval_expr cx e
Proof
  strip_tac >> rw[FUN_EQ_THM] >>
  simp[Once evaluate_def, builtin_args_length_ok_def, code_slice_source_def,
       is_self_codesize_def, type_check_def, assert_def, ignore_bind_def,
       return_def, bind_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def] >>
  Cases_on `eval_expr cx e x` >> rename1 `_ = (res,st')` >> Cases_on `res` >>
  gvs[] >> drule_all named_const_operand_eval_value >> strip_tac >>
  simp[read_result_def, return_def, Once evaluate_def, get_accounts_def,
       evaluate_builtin_def, lift_sum_def, precompile_call_success_def,
       bind_def, ignore_bind_def]
QED

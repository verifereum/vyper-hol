(* Singleton type-builtins raise before returning a raw expression value.
   Failure of a later read_result alone would not establish this fact. *)
Theory typeBuiltinSource
Ancestors
  vyperInterpreter vyperContext vyperState vyperValue vyperAST

Theorem eval_type_builtin_singleton_error:
  !cx ann tb ty e es v ee err.
    type_builtin_args_length_ok tb 1 /\
    bind (eval_expr cx e) (read_result cx) es = (INL v, ee) /\
    evaluate_type_builtin cx tb ty [expr_type e] [v] = INR err ==>
    eval_expr cx (TypeBuiltin ann tb ty [e]) es =
      (INR (Error err), ee)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_expr cx e es` >>
  rename1 `eval_expr cx e es = (child_result, child_state)` >>
  Cases_on `child_result` >>
  gvs[bind_def] >>
  simp[Once evaluate_def, ignore_bind_def, type_check_def,
       assert_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, return_def, bind_def, lift_sum_def, raise_def]
QED

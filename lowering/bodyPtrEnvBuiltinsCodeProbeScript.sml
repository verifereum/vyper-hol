(* Bare .code is excluded by the existing allocation precondition. *)
Theory bodyPtrEnvBuiltinsCodeProbe
Ancestors
  bodyPtrPreds exprSimHypsDefs allocLimits vyperAST

Theorem bare_code_body_pre_impossible:
  ~expr_body_pre cenv cx env (Builtin ann (Acc Code) args) es
Proof
  simp[expr_body_pre_def, Once alloc_limits_expr_def]
QED

Theorem body_code_ptr_case:
  body_expr_ptr_ok cx (Builtin ann (Acc Code) args)
Proof
  simp[body_expr_ptr_ok_def, bare_code_body_pre_impossible]
QED

(*
 * Expression simulation: a bare x.code (outside slice).
 *
 * compile_acc_code_case, the case lemma exprSimBuiltins re-exports for
 * compile_expr_sim (exprSimMain).  It holds vacuously: Python's codegen
 * rejects .code outside slice()'s source (CompilerPanic ".code requires
 * slice() context"), and so does the lowering's allocation check
 * (alloc_limits_expr), which expr_body_pre carries.
 *)

Theory exprSimAccCode
Ancestors
  exprSimHypsDefs vyperAST

Theorem compile_acc_code_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Acc Code) args)
Proof
  simp[expr_vv_case_def, expr_body_pre_def, allocLimitsTheory.alloc_limits_expr_def]
QED

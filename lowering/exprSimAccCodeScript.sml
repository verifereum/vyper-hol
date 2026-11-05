(*
 * Expression simulation: a bare x.code (outside slice).
 *
 * compile_acc_code_case, the case lemma exprSimBuiltins re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimAccCode
Ancestors
  exprSimHypsDefs vyperAST

Theorem compile_acc_code_case:
  !nocalls ctx func cenv cx ann args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Acc Code) args)
Proof
  cheat
QED

(*
 * Expression simulation: concat(...).
 *
 * compile_concat_case, the case lemma exprSimBuiltins re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimConcat
Ancestors
  exprSimHypsDefs vyperAST

Theorem compile_concat_case:
  !nocalls ctx func cenv cx ann n args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Concat n) args)
Proof
  cheat
QED

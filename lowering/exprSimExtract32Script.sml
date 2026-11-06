(*
 * Expression simulation: extract32(b, start).
 *
 * compile_extract32_case, the case lemma exprSimBuiltins re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimExtract32
Ancestors
  exprSimHypsDefs vyperAST

Theorem compile_extract32_case:
  !nocalls ctx func cenv cx ann t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Extract32 t args)
Proof
  cheat
QED

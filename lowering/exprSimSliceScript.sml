(*
 * Expression simulation: slice(b, start, length), including x.code and msg.data sources.
 *
 * compile_slice_case, the case lemma exprSimBuiltins re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimSlice
Ancestors
  exprSimHypsDefs vyperAST

Theorem compile_slice_case:
  !nocalls ctx func cenv cx ann n args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (Builtin ann (Slice n) args)
Proof
  cheat
QED

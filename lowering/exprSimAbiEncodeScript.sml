(*
 * Expression simulation: abi_encode.
 *
 * compile_abi_encode_case, the case lemma exprSimAggregates re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimAbiEncode
Ancestors
  exprSimHypsDefs vyperAST

Theorem compile_abi_encode_case:
  !nocalls ctx func cenv cx ann ensure mid t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann (AbiEncode ensure mid) t args)
Proof
  cheat
QED

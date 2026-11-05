(*
 * Expression simulation: abi_decode, with its validation aborts.
 *
 * compile_abi_decode_case, the case lemma exprSimAggregates re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimAbiDecode
Ancestors
  exprSimHypsDefs vyperAST

Theorem compile_abi_decode_case:
  !nocalls ctx func cenv cx ann unwrap t args.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann (AbiDecode unwrap) t args)
Proof
  cheat
QED

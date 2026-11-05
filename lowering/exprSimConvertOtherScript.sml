(*
 * Expression simulation: the conversions exprSimConvert does not cover: to or from decimal, address, bytesM, bytestrings and flags.
 *
 * compile_convert_other_case, the case lemma exprSimAggregates re-exports for compile_expr_sim
 * (exprSimMain): from exprs_case of the operands, expr_vv_case of the
 * builtin.
 *)

Theory exprSimConvertOther
Ancestors
  exprSimHypsDefs exprSimConvert vyperAST

Theorem compile_convert_other_case:
  !nocalls ctx func cenv cx ann t args.
    exprs_case nocalls ctx func cenv cx args /\
    ~(?e1. args = [e1] /\ int_convert_pair (expr_type e1) t) ==>
    expr_vv_case nocalls ctx func cenv cx (TypeBuiltin ann Convert t args)
Proof
  cheat
QED

Theory bodyFullTypeBuiltin
Ancestors
  bodyFullTypeBuiltinEmpty bodyFullTypeBuiltinWords bodyFullTypeBuiltinConvert
  bodyFullTypeBuiltinExtract32 bodyFullTypeBuiltinAbiDecode bodyFullTypeBuiltinAbiEncode
  bodyFullPreds vyperAST vyperInterpreter vyperState list

Theorem type_builtin_expr_full_ok:
  !cx v11 tb typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (TypeBuiltin v11 tb typ es)
Proof
  rpt gen_tac >> Cases_on `tb`
  >- MATCH_ACCEPT_TAC empty_expr_full_ok
  >- simp[bound_builtin_expr_full_ok]
  >- simp[bound_builtin_expr_full_ok]
  >- simp[bound_builtin_expr_full_ok]
  >- MATCH_ACCEPT_TAC convert_expr_full_ok
  >- MATCH_ACCEPT_TAC extract32_expr_full_ok
  >- MATCH_ACCEPT_TAC abi_decode_expr_full_ok >>
  MATCH_ACCEPT_TAC abi_encode_expr_full_ok
QED

Theory bodyFullTypeBuiltinAbiDecode
Ancestors
  bodyFullPreds bodyFullOfVV bodyFullExprGeneric bodyFullAllocGeneric
  gasOutcomeFullCompose exprSimHyps exprSimSource exprSimAbiDecode
  vyperContext vyperInterpreter vyperState vyperAST

Theorem abi_decode_expr_full_ok:
  !cx v11 b typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiDecode b) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (TypeBuiltin v11 (AbiDecode b) typ es)
Proof
  cheat
QED

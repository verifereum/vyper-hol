Theory bodyFullTypeBuiltinAbiEncode
Ancestors
  bodyFullPreds bodyFullOfVV bodyFullExprGeneric bodyFullAllocGeneric
  gasOutcomeFullCompose exprSimHyps exprSimSource exprSimAbiEncode
  vyperContext vyperInterpreter vyperState vyperAST

Theorem abi_encode_expr_full_ok:
  !cx v11 b m typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok (AbiEncode b m) (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (TypeBuiltin v11 (AbiEncode b m) typ es)
Proof
  cheat
QED

Theory bodyFullTypeBuiltinConvert
Ancestors
  bodyFullPreds bodyFullOfVV bodyFullExprGeneric bodyFullAllocGeneric
  gasOutcomeFullCompose exprSimHyps exprSimSource exprSimConvert
  vyperContext vyperInterpreter vyperState vyperAST

Theorem convert_expr_full_ok:
  !cx v11 typ es.
    (!s'' x t.
       type_check (type_builtin_args_length_ok Convert (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ==>
       body_exprs_full_ok cx es) ==>
    body_expr_full_ok cx (TypeBuiltin v11 Convert typ es)
Proof
  cheat
QED

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
  rpt gen_tac >> strip_tac >>
  simp[body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `body_exprs_full_ok cx [e1]` by
    (first_x_assum irule >>
     simp[type_builtin_args_length_ok_def, type_check_def,
          assert_def, return_def] >> metis_tac[]) >>
  FAIL_TAC "convert child assembly"
QED

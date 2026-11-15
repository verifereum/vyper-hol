Theory bodyFullTypeBuiltinConvert
Ancestors
  bodyFullPreds bodyFullOfVV bodyFullExprGeneric bodyFullAllocGeneric
  bodyFullConvertScalarJoint bodyFullConvertDynamicJoint bodyFullConvertBytesJoint
  bodyFullConvertValueBridge
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
  `body_expr_full_ok cx e1` by gvs[body_exprs_full_ok_def] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (TypeBuiltin typ Convert typ [e1]) es'` by
    (Cases_on `is_bytestring_type typ`
     >- (irule convert_bytes_vv_sim_full >> simp[] >> metis_tac[]) >>
     Cases_on `is_bytestring_type (expr_type e1)`
     >- (irule convert_dynamic_vv_sim_full >> simp[] >> metis_tac[]) >>
     irule convert_scalar_vv_sim_full >> simp[] >> metis_tac[]) >>
  conj_tac >- (irule convert_sim_full_of_vv >> simp[] >> metis_tac[]) >>
  simp[]
QED

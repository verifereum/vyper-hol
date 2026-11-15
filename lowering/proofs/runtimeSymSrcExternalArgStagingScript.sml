Theory runtimeSymSrcExternalArgStaging
Ancestors
  runtimeSymSrcContextComplete runtimeSymSrcInterfaces runtimeSymSrcEmission
  exprLowering context compileEnv emitHelper loweringShapeDefs list
  supportedExprs supportedExprTraverse

Theorem runtime_sym_ext_call_arg_value:
  runtime_sym_value vv ==> runtime_sym_value (ext_call_arg_value ty vv)
Proof
  Cases_on `vv` >> simp[ext_call_arg_value_def, runtime_sym_value_def]
QED

Theorem runtime_sym_ext_call_args:
  !es tys cfn ce kw_es s vals s'.
  runtime_sym_env ce /\ EVERY (supported_pure_expr tops) es /\
  ~supported_exprs_exists is_self_code es /\
  (!e t. MEM e es ==> runtime_sym_expr_contract tops cfn ce t e) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_ext_call_args cfn ce kw_es tys es s = (vals,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ EVERY runtime_sym_value vals
Proof
  Induct >- (Cases >> simp[compile_ext_call_args_def, comp_return_def]) >>
  Cases_on `tys` >- simp[compile_ext_call_args_def, comp_return_def] >>
  rpt gen_tac >>
  simp[Once compile_ext_call_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `cfn ce (expr_type e) e s = _` >>
  `runtime_sym_expr_contract tops cfn ce (expr_type e) e` by metis_tac[] >>
  fs[supported_expr_exists_def] >>
  qpat_x_assum `runtime_sym_expr_contract _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[runtime_sym_expr_contract_def] >>
  disch_then (drule_at (Pat `cfn _ _ _ _ = _`)) >>
  simp[] >> (impl_tac >- gvs[supported_expr_def]) >> strip_tac >>
  drule runtime_sym_ext_call_arg_value >> strip_tac >>
  drule_at (Pat `compile_snapshot_vv _ _ _ _ = _`) runtime_sym_snapshot_vv >>
  simp[] >> strip_tac >>
  first_x_assum (drule_at (Pat `compile_ext_call_args _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >> gvs[]
QED

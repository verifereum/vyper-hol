Theory runtimeSymSrcExternalCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  runtimeSymSrcContextComplete exprLowering compileEnv emitHelper loweringShapeDefs
  list venomInst stackPlanTypes supportedExprs supportedExprTraverse

Theorem runtime_sym_ext_call_kwarg:
  runtime_sym_lower_value_clause tops ==>
  !cfn ce rt k e s op ty s'.
    (!t. runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\ supported_expr tops e /\
    ~supported_expr_exists is_self_code e /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_ext_call_kwarg cfn ce rt k e s = ((op,ty),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  rewrite_tac[runtime_sym_lower_value_clause_def] >> strip_tac >>
  rpt gen_tac >> simp[compile_ext_call_kwarg_def] >>
  IF_CASES_TAC >> simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac
  >- (qpat_x_assum `!t. runtime_sym_expr_contract tops cfn ce t e`
        (qspec_then `expr_type e` mp_tac) >>
      pure_rewrite_tac[runtime_sym_expr_contract_def] >>
      disch_then (qspecl_then [`s`, `vv`, `cs'`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >>
      drule_all runtime_sym_materialize_vv >> simp[]) >>
  gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem runtime_sym_ext_call_kwargs:
  runtime_sym_lower_value_clause tops ==>
  !ks es cfn ce rt s vo go d s'.
    (!e t. MEM e es ==> runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\ EVERY (supported_expr tops) es /\
    EVERY (\e. ~supported_expr_exists is_self_code e) es /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_ext_call_kwargs cfn ce rt ks es s = ((vo,go,d),s') ==>
    EVERY runtime_sym_inst (state_insts s') /\
    (!v. vo = SOME v ==> ~is_label_operand v) /\
    (!g. go = SOME g ==> ~is_label_operand g) /\
    (!v ty. d = SOME (v,ty) ==> ~is_label_operand v)
Proof
  strip_tac >> Induct >> Cases_on `es` >>
  simp[compile_ext_call_kwargs_def, comp_return_def, comp_bind_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  `EVERY runtime_sym_inst (state_insts cs') /\ ~is_label_operand op` by
    (drule runtime_sym_ext_call_kwarg >>
     disch_then (drule_at (Pos last)) >> simp[]) >>
  gvs[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  first_x_assum (drule_at (Pos last)) >> simp[] >> strip_tac >>
  Cases_on `h' = EKValue` >> gvs[comp_return_def] >>
  Cases_on `h' = EKGas` >> gvs[comp_return_def]
QED

Theorem runtime_sym_call_raw:
  !tops cfn ce rt ty rcf es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\
    supported_expr tops (Call rt (RawCallTarget rcf) es default) /\
    ~supported_expr_exists is_self_code (Call rt (RawCallTarget rcf) es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) (RawCallTarget rcf) es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  Cases_on `default` >>
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED

Theorem runtime_sym_call_raw_calldata:
  !tops cfn ce rt ty rcf es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
           runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\
    supported_expr tops (Call rt (RawCallCalldataTarget rcf) es default) /\
    ~supported_expr_exists is_self_code (Call rt (RawCallCalldataTarget rcf) es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) (RawCallCalldataTarget rcf) es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  Cases_on `default` >>
  simp[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def]
QED

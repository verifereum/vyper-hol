Theory runtimeSymSrcExternalCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  runtimeSymSrcContextComplete exprLowering context compileEnv emitHelper loweringShapeDefs
  list rich_list venomInst stackPlanTypes supportedExprs supportedExprTraverse

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

Theorem runtime_sym_gas_option[local]:
  (!g. opt = SOME g ==> ~is_label_operand g) /\
  EVERY runtime_sym_inst (state_insts s) /\
  (case opt of NONE => emit_op GAS [] s | SOME g => (g,s)) = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `opt` >> simp[] >> strip_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[]
QED

Theorem runtime_sym_default_option[local]:
  (!v ty. opt = SOME (v,ty) ==> ~is_label_operand v) /\
  (case opt of NONE => (F,Lit 0w,rt) | SOME (d,dt) => (T,d,dt)) =
    (hasdef,op,ty) ==> ~is_label_operand op
Proof
  Cases_on `opt` >- simp[is_label_operand_def] >>
  rename1 `SOME p` >> PairCases_on `p` >> simp[] >> metis_tac[]
QED

Theorem runtime_sym_call_external_cond:
  (!ce addr vals tys am aa mid ra mn rm static value gas skip hasdef def rt dt enc dec s op s'.
    runtime_sym_env ce /\ EVERY runtime_sym_value vals /\
    ~is_label_operand addr /\ ~is_label_operand value /\
    ~is_label_operand gas /\ ~is_label_operand def /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_external_call_kwargs ce addr vals tys am aa mid ra mn rm
      static value gas skip hasdef def rt dt enc dec s = (op,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) /\
  runtime_sym_multi_vvs_clause tops /\ runtime_sym_lower_value_clause tops ==>
  !cfn ce rt ty static skip fname ats ret opts es default s v s'.
    (!e t. MEM e es \/ default = SOME e ==>
      runtime_sym_expr_contract tops cfn ce t e) /\
    runtime_sym_env ce /\
    supported_expr tops (Call rt (ExtCall static skip (fname,ats,ret) opts) es default) /\
    ~supported_expr_exists is_self_code
      (Call rt (ExtCall static skip (fname,ats,ret) opts) es default) /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_call cfn ce rt (ty : type) (ExtCall static skip (fname,ats,ret) opts)
      es default s = (v,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `EVERY (supported_pure_expr tops) es` by
    (Cases_on `default` >>
     gvs[supported_expr_def, supported_pure_expr_def,
         supported_effect_expr_def, supported_pure_exprs_every]) >>
  `~supported_exprs_exists is_self_code es` by
    gvs[supported_expr_exists_def] >>
  qpat_x_assum `compile_call _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `es` >> simp[Once compile_call_def]
  >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
      simp[runtime_sym_value_def, is_label_operand_def] >>
      irule runtime_sym_emit_inst >>
      qexistsl [`0`, `INVALID`, `[]`, `[]`, `s`, `()`] >>
      simp[runtime_sym_inst_def, mk_inst_def]) >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  `EVERY runtime_sym_inst (state_insts st1) /\ ~is_label_operand addr_op` by
    (qpat_x_assum `runtime_sym_lower_value_clause tops` mp_tac >>
     rewrite_tac[runtime_sym_lower_value_clause_def] >> strip_tac >>
     first_x_assum irule >>
     gvs[supported_expr_exists_def, supported_expr_def] >> metis_tac[]) >>
  `EVERY runtime_sym_inst (state_insts st2) /\ EVERY runtime_sym_value arg_vals` by
    (qpat_x_assum `runtime_sym_multi_vvs_clause tops` mp_tac >>
     rewrite_tac[runtime_sym_multi_vvs_clause_def] >> strip_tac >>
     first_x_assum irule >>
     gvs[supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS, EVERY_MEM] >>
     metis_tac[MEM_TAKE]) >>
  drule runtime_sym_ext_call_kwargs >>
  disch_then (drule_at (Pos last)) >>
  (impl_tac >-
    (qpat_x_assum `EVERY (supported_pure_expr tops) _` mp_tac >>
     qpat_x_assum `~supported_exprs_exists is_self_code _` mp_tac >>
     simp[EVERY_MEM, supported_exprs_exists_every, GSYM EVERY_NOT_EXISTS,
          supported_expr_def] >> rpt strip_tac >>
     drule MEM_DROP_IMP >> strip_tac >> metis_tac[MEM])) >>
  strip_tac >>
  drule_all runtime_sym_gas_option >> strip_tac >>
  `~is_label_operand (case value_opt of NONE => Lit 0w | SOME x => x)` by
    (Cases_on `value_opt` >> simp[is_label_operand_def]) >>
  drule_all runtime_sym_default_option >> strip_tac >>
  qpat_x_assum `!ce addr vals tys am aa mid ra mn rm static value gas skip hasdef def rt dt enc dec s op s'. _`
    (drule_at (Pat `compile_external_call_kwargs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> strip_tac >>
  Cases_on `ret = NoneT` >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  simp[] >> strip_tac >> gvs[runtime_sym_value_def, mk_ptr_def, base_ptr_def]
QED

Theory bodyPtrPopCallBoundary
Ancestors bodyPtrPopTraversalBoundary bodyPtrPopExternalBoundary
  bodyPtrPopPrecompileBoundary
  bodyPtrPopCompileDomain bodyPtrPopCompilerBoundary bodyPtrPopMaterialization
  bodyPtrPopAllocationBoundary bodyPtrPopArithmeticBoundary
  exprLowering emitHelper compileEnv list supportedExprs vyperAST

Theorem pop_fresh_vars_boundary:
  !n sa r sb. pop_comp_boundary sa /\ fresh_vars n sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Induct >> simp[fresh_vars_def, comp_return_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_fresh_var_boundary >> simp[]) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  rpt strip_tac >> gvs[comp_return_def]
QED

Theorem pop_emit_multi_op_boundary:
  opc <> ASSERT /\ pop_comp_boundary sa /\
  emit_multi_op opc ops n sa = (r,sb) ==> pop_comp_boundary sb
Proof
  simp[emit_multi_op_def, comp_ignore_bind_def] >> rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all pop_fresh_vars_boundary >> simp[]) >>
  rpt strip_tac >>
  dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]) >>
  rpt strip_tac >> gvs[comp_return_def]
QED

Theorem pop_compile_intcall_boundary:
  (!e aty s v t. MEM e args /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_call cfn cenv rt ty (IntCall fid) args default_ret sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_call_def] >> rpt strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `compile_multi_vvs _ _ _ _ = _`)
       pop_compile_multi_vvs_boundary >> disch_then irule >> simp[] >>
     first_assum MATCH_ACCEPT_TAC) >>
  Cases_on `returns_count > 0` >> Cases_on `return_buf_size > 0` >>
  gvs[] >>
  imp_res_tac pop_compile_alloc_buffer_boundary >>
  drule_all pop_compile_stage_intcall_args_boundary >> strip_tac >>
  imp_res_tac pop_emit_multi_op_boundary >>
  imp_res_tac pop_emit_void_boundary >>
  imp_res_tac pop_emit_op_boundary >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[] >> drule_all pop_store_multi_results_boundary >> simp[]
QED

Theorem pop_guard_pair_boundary[local]:
  opc <> SUB /\ opc <> ISZERO /\ pop_comp_boundary sa /\
  emit_op opc ops sa = (v,sm) /\ emit_void ASSERT [v] sm = (u,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >> irule pop_staticcall_guard_boundary >>
  qexistsl_tac [`ops`, `opc`, `u`, `sa`] >> simp[comp_bind_def]
QED


Theorem pop_compile_send_boundary:
  (!e aty s v t. MEM e args /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_call cfn cenv rt ty (Send has_gas) args default_ret sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `args` >> simp[compile_call_def]
  >- (rpt strip_tac >> pairarg_tac >> gvs[] >>
      drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]) >>
  Cases_on `t` >> simp[compile_call_def]
  >- (rpt strip_tac >> pairarg_tac >> gvs[] >>
      drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]) >>
  Cases_on `LENGTH t' = if has_gas then 1 else 0` >> simp[compile_call_def]
  >- (rpt strip_tac >>
      `!e aty s v t. (e = h \/ e = h' \/ MEM e t') /\
        pop_comp_boundary s /\ lower_value cfn cenv aty e s = (v,t) ==>
        pop_comp_boundary t` by
        (rpt strip_tac >> drule_at (Pat `lower_value _ _ _ _ _ = _`)
          pop_lower_value_boundary >> disch_then irule >> simp[] >>
         rpt strip_tac >> qpat_x_assum `!e aty s v t. _`
           (qspec_then `e` mp_tac) >> simp[] >> disch_then drule_all >> simp[]) >>
      Cases_on `has_gas` >> Cases_on `t'` >>
      gvs[IgnAsm `!e aty s v t. _`] >>
      qpat_x_assum `!e aty s v t. _ /\ _ /\ cfn _ _ _ _ = _ ==> _` kall_tac >>
      pairarg_tac >> gvs[IgnAsm `!e aty s v t. _`] >>
      pairarg_tac >> gvs[IgnAsm `!e aty s v t. _`] >>
      pairarg_tac >> gvs[IgnAsm `!e aty s v t. _`] >>
      pairarg_tac >> gvs[IgnAsm `!e aty s v t. _`]
      >- (pairarg_tac >> gvs[IgnAsm `!e aty s v t. _`] >>
          ntac 3 (qpat_assum `!e aty s v t. _` (fn th => imp_res_tac th)) >>
          gvs[IgnAsm `!e aty s v t. _`] >>
          drule_at (Pat `emit_op _ _ _ = _`) pop_guard_pair_boundary >> simp[]) >>
      ntac 2 (qpat_assum `!e aty s v t. _` (fn th => imp_res_tac th)) >>
      gvs[IgnAsm `!e aty s v t. _`] >>
          drule_at (Pat `emit_op _ _ _ = _`) pop_guard_pair_boundary >> simp[]) >>
  rpt strip_tac >> pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]
QED

Theorem pop_compile_extcall_boundary:
  (!e aty s v t. MEM e args /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_comp_boundary sa /\
  compile_call cfn cenv rt ty (ExtCall stat skip sig opts) args default_ret sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  PairCases_on `sig` >> Cases_on `args` >> simp[compile_call_def]
  >- (rpt strip_tac >> pairarg_tac >> gvs[] >>
      drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[]) >>
  rpt strip_tac >>
  pairarg_tac >> gvs[IgnAsm `!e aty s v t. _`] >>
  `pop_comp_boundary st1` by
    (drule_at (Pat `lower_value _ _ _ _ _ = _`) pop_lower_value_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!e aty s v t. _` (qspec_then `h` mp_tac) >>
     simp[] >> disch_then drule_all >> simp[]) >>
  pairarg_tac >> gvs[IgnAsm `!e aty s v t. _`] >>
  `pop_comp_boundary st2` by
    (drule_at (Pat `compile_multi_vvs _ _ _ _ = _`) pop_compile_multi_vvs_boundary >>
     disch_then irule >> simp[] >> rpt strip_tac >>
     `MEM e t` by metis_tac[rich_listTheory.MEM_TAKE] >>
     qpat_x_assum `!e aty s v t. _` (qspec_then `e` mp_tac) >>
     simp[] >> disch_then drule_all >> simp[]) >>
  pairarg_tac >> gvs[IgnAsm `!e aty s v t. _`] >>
  `pop_comp_boundary st3` by
    (drule_at (Pat `compile_ext_call_kwargs _ _ _ _ _ _ = _`)
       pop_compile_ext_call_kwargs_boundary >> disch_then irule >> simp[] >>
     rpt strip_tac >> `MEM e t` by metis_tac[rich_listTheory.MEM_DROP_IMP] >>
     qpat_x_assum `!e aty s v t. _` (qspec_then `e` mp_tac) >>
     simp[] >> disch_then drule_all >> simp[]) >>
  qpat_x_assum `!e aty s v t. _` kall_tac >>
  Cases_on `default_opt` >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  Cases_on `gas_opt` >> gvs[] >>
  imp_res_tac pop_emit_op_boundary >> gvs[] >>
  drule_all pop_compile_external_call_kwargs_boundary >> strip_tac >>
  gvs[AllCaseEqs()]
QED

Theorem pop_compile_call_boundary:
  (!cenv aty e s v t. pop_compile_domain tops e /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_compile_domain tops (Call rt target args default_ret) /\
  pop_comp_boundary sa /\
  compile_call cfn cenv rt ty target args default_ret sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  rpt strip_tac >>
  `default_ret = NONE` by metis_tac[pop_domain_call_default] >> gvs[] >>
  `EVERY (supported_pure_expr tops) args` by
    (drule_all pop_domain_call_args >> simp[]) >>
  `!e aty s v t. MEM e args /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t` by
    (rpt strip_tac >>
     `pop_compile_domain tops e` by (drule_all pop_domain_pure_argument >> simp[]) >>
     first_x_assum drule_all >> simp[]) >>
  drule pop_domain_call_support >> strip_tac >>
  Cases_on `target` >>
  FIRST [drule_all pop_compile_intcall_boundary,
         drule_all pop_compile_extcall_boundary,
         drule_all pop_compile_send_boundary,
         (gvs[oneline supported_effect_expr_def] >> Cases_on `rt` >> gvs[]) ] >> simp[]
QED

Theorem pop_compile_expr_body_call_boundary:
  (!cenv aty e s v t. pop_compile_domain tops e /\ pop_comp_boundary s /\
    cfn cenv aty e s = (v,t) ==> pop_comp_boundary t) /\
  pop_compile_domain tops (Call rt target args default_ret) /\
  pop_comp_boundary sa /\
  compile_expr_body cfn bfn tfn cenv ty (Call rt target args default_ret) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  simp[compile_expr_body_def, expr_type_def] >> rpt strip_tac >>
  drule_all pop_compile_call_boundary >> simp[]
QED

Theory ctorDeployMemoryRunMemPrefixLayout
Ancestors
  ctorDeployMemoryRunMemEntryLabel
  ctorDeployMemoryRunMemPrefixSource ctorDeployInitcode ctorDeployShape
  ctorDeployLoweringCode ctorDeployLoweringDefs ctorDeployDefs e2eDeployDefs
  compileVyper moduleLowering compileEnv loweringStateRelDefs fragExec vyperCompiler context
  supportedProgram supportedNames ctorRegisterArgs deployUnitProducers venomInst e2eEntry o1PassContract venomState vyperTypeContractSoundness words loweringShapeProps loweringShapeSource ctorGeneratorShape list ctorUnitShape loweringShapeDefs

Theorem ctor_prefix_package_nonpayable:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  classify_functions tops = (exts,ints,fb,SOME cf) /\
  vyperInterpreter$lookup_function NONE "__init__" Deploy tops =
    SOME (mut,F,args,[],NoneT,ffbody) /\ mut <> Payable /\
  set_constructor_package_target rpolicy.rpol_target
    (package_constructor tops T (K global_nonreentrant_slot) cf) =
    (cenv,pos_args,pay,nr,nkey,ut,cb,ret) ==>
  ~pay
Proof
  rpt strip_tac >>
  drule lower_vyper_deploy_unit_ctor_named_init >>
  qspecl_then [`tops`,`NONE`,`"__init__"`] mp_tac
    classify_functions_ctor_lookup >>
  PairCases_on `cf` >>
  gvs[ctor_named_init_def, package_constructor_def,
      set_constructor_package_target_def]
QED

Theorem ctor_prefix_fixed_appends:
  cs_appends (compile_fixed_region_with_id cap)
Proof
  simp[compile_fixed_region_with_id_def] >>
  irule cs_appends_bind >> simp[cs_appends_prims] >> gen_tac >>
  irule cs_appends_bind >> simp[cs_appends_prims] >> gen_tac >>
  irule cs_appends_ignore_bind >> simp[cs_appends_prims, cs_appends_return]
QED

Theorem ctor_prefix_lock_appends:
  cs_appends (compile_nonreentrant_lock key trans view)
Proof
  rw[compile_nonreentrant_lock_def] >>
  rpt (irule cs_appends_bind >>
       simp[cs_appends_emit_helpers] >> gen_tac) >>
  irule cs_appends_ignore_bind >>
  simp[cs_appends_emit_helpers, cs_appends_return]
QED

Theorem ctor_prefix_code_restrict:
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (fbody,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,se,sp,sf,func) /\
  (!ce args pay nr key ut fbody ret.
    set_constructor_package_target rpolicy.rpol_target
      (package_constructor tops T (K global_nonreentrant_slot) cf) =
        (ce,args,pay,nr,key,ut,fbody,ret) ==> ~pay) /\
  classify_functions tops = (exts,ints,fb,SOME cf) ==>
  ?cv nv s1 s2 st_pay.
    emit_op CALLVALUE [] (initial_compile_state "__deploy") = (cv,s1) /\
    emit_op ISZERO [cv] s1 = (nv,s2) /\
    emit_void ASSERT [nv] s2 = ((),st_pay) /\
    fn_has_code (initial_compile_state "__deploy") st_pay func
Proof
  pure_rewrite_tac[deploy_ctor_code_def] >> rpt strip_tac >> gvs[] >>
  gvs[comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `cs_extends st_pay st1` by
    (Cases_on `imm_len tops > 0` >> gvs[comp_return_def, cs_extends_refl] >>
     qpat_x_assum `comp_bind _ _ st_pay = _` mp_tac >>
     simp[comp_bind_def, comp_return_def] >> pairarg_tac >> simp[] >>
     metis_tac[ctor_prefix_fixed_appends, cs_appends_def]) >>
  `cs_extends st1 st2` by metis_tac[ctor_registration_extends] >>
  `cs_extends st2 st3` by
    (Cases_on `nr` >> gvs[comp_return_def] >>
     metis_tac[ctor_prefix_lock_appends, cs_appends_def, cs_extends_refl]) >>
  `cs_extends st3 sa` by metis_tac[cs_appends_prims, cs_appends_def] >>
  `cs_extends st_pay sa` by metis_tac[cs_extends_trans] >>
  `cs_extends (initial_compile_state "__deploy") cs'` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends cs' cs''` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends cs'' st_pay` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends (initial_compile_state "__deploy") st_pay` by
    metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  qexistsl [`cv`,`no_val`,`cs'`,`cs''`,`st_pay`] >> simp[]
QED

Theorem ctor_prefix_function_identity:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  MEM func dunit.cu_context.ctx_functions /\ func.fn_name = "__deploy" /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn ==>
  func = fn
Proof
  rpt strip_tac >>
  drule lower_vyper_deploy_unit_context_ok >>
  simp[lowering_context_ok_def] >> strip_tac >>
  drule lookup_function_MEM >> strip_tac >>
  drule lookup_function_result_name >> strip_tac >>
  irule distinct_function_names_unique >>
  conj_tac >- (qexists `"__deploy"` >> simp[]) >>
  qexists `dunit.cu_context.ctx_functions` >> gvs[ctx_fn_names_def]
QED

Theorem ctor_prefix_rejecting_code:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\
  deploy_source_ok tops am tx /\ deploy_state_rel tops (assemble prog') am tx es /\
  classify_functions tops = (exts,ints,fb,SOME cf) /\
  (!mut nr fbody am_c es0.
    ~deploy_ctor_start tops am tx (mut,nr,fbody,am_c,es0)) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn ==>
  ?cv nv s1 s2 st_pay.
    emit_op CALLVALUE [] (initial_compile_state "__deploy") = (cv,s1) /\
    emit_op ISZERO [cv] s1 = (nv,s2) /\
    emit_void ASSERT [nv] s2 = ((),st_pay) /\
    fn_has_code (initial_compile_state "__deploy") st_pay fn
Proof
  rpt strip_tac >>
  drule_all ctor_prefix_source_obstruction >> strip_tac >>
  drule_all deploy_ctor_code_exists >> strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
   MEM func dunit.cu_context.ctx_functions /\ func.fn_name = "__deploy"`
    by fs[deploy_ctor_code_def] >>
  `func = fn` by (irule ctor_prefix_function_identity >> simp[] >> metis_tac[]) >>
  gvs[] >> drule ctor_prefix_code_restrict >>
  disch_then (qspecl_then [`ints`,`fb`,`exts`,`cf`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    drule_all ctor_prefix_package_nonpayable >> simp[])) >>
  metis_tac[]
QED

Theorem ctor_prefix_entry_fresh:
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  fresh_vars_wrt (initial_compile_state "__deploy")
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
Proof
  simp[gas_variant_def] >>
  disch_then (mp_tac o Q.AP_TERM `\s. s.vs_vars`) >>
  simp[deploy_entry_state_def, entry_venom_state_def, init_venom_state_def,
       fresh_vars_wrt_def]
QED

Theorem ctor_prefix_entry_value:
  deploy_source_ok tops am tx /\ deploy_state_rel tops deploy_bc am tx es /\
  gas_variant vs (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) /\ tx.value <> 0 ==>
  (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>).
    vs_call_ctx.cc_callvalue <> 0w
Proof
  rpt strip_tac >>
  `tx.value < 2 ** 256` by
    fs[deploy_source_ok_def, deploy_typing_ok_constants_ready, call_tx_well_typed_def] >>
  `vs.vs_call_ctx.cc_callvalue = n2w tx.value` by
    (qpat_x_assum `gas_variant _ _` mp_tac >> simp[gas_variant_def] >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx.cc_callvalue`) >>
     qpat_x_assum `deploy_state_rel _ _ _ _ _` mp_tac >>
     simp[deploy_state_rel_def] >> rpt strip_tac >>
     gvs[opt_deploy_entry_state_own_def, opt_entry_state_own_def, entry_venom_state_def]) >>
  gvs[n2w_11, dimword_def]
QED

Theorem ctor_prefix_entry_not_halted:
  gas_variant vs (opt_deploy_entry_state_own prog prog' cplan tops es with vs_outcomes := vs.vs_outcomes) ==>
  ~(vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
               vs_inst_idx := 0 |>).vs_halted
Proof
  simp[gas_variant_def] >>
  disch_then (mp_tac o Q.AP_TERM `\s. s.vs_halted`) >>
  simp[opt_deploy_entry_state_own_def, opt_entry_state_own_def, entry_venom_state_def, init_venom_state_def]
QED

Theorem ctor_prefix_task_entry_label:
  deploy_phases policy tops (deploy_bc,runtime_bc)
    (rpolicy,dunit,dout,prog,cplan) /\ deploy_source_ok tops am tx /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  lbl = "__deploy"
Proof
  rpt strip_tac >>
  `lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
   supported_program tops /\ supported_program_deploy tops` by
    fs[deploy_phases_def, deploy_source_ok_def] >>
  drule_all ctor_checked_entry_label_from_lowering >> simp[]
QED

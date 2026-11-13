Theory ctorDeployMemoryRunMemEntryBoundary
Ancestors
  ctorDeployLoweringDefs deployUnitProducers vyperCompiler venomInst list
  moduleLowering context compileVyper compileEnv
  ctorDeployDefs e2eEntry o1PassContract allocaHistory venomState

Theorem ctor_checked_lookup_identity:
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
  MEM func dunit.cu_context.ctx_functions /\ func.fn_name = "__deploy" /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn ==>
  fn = func
Proof
  strip_tac >> drule lower_vyper_deploy_unit_context_ok >>
  simp[lowering_context_ok_def, ctx_fn_names_def] >> strip_tac >>
  drule lookup_function_result_name >> strip_tac >>
  drule lookup_function_MEM >> strip_tac >>
  metis_tac[distinct_function_names_unique]
QED

Theorem ctor_checked_code_lookup_identity:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func fn.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) /\
  lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME fn ==>
  fn = func
Proof
  simp[deploy_ctor_code_def] >> rpt strip_tac >>
  drule_all ctor_checked_lookup_identity >> simp[]
QED

Theorem ctor_checked_registration_return_buf:
  !args cenv off dsz st cenv' st'.
    compile_register_constructor_args cenv args off dsz st = (cenv',st') ==>
    cenv'.ce_return_buf = cenv.ce_return_buf
Proof
  Induct >- simp[compile_register_constructor_args_def, comp_return_def] >>
  PairCases >> rpt gen_tac >>
  Cases_on `FLOOKUP cenv.ce_vars h0` >>
  simp[Once compile_register_constructor_args_def] >- metis_tac[] >>
  rename1 `FLOOKUP cenv.ce_vars h0 = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> simp[] >- metis_tac[] >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem ctor_checked_package_return_buf:
  !tops use_trans nkeys cf target cenv pos_args payable nr nkey ut body ret.
  set_constructor_package_target target
    (package_constructor tops use_trans nkeys cf) =
      (cenv,pos_args,payable,nr,nkey,ut,body,ret) ==>
  cenv.ce_return_buf = NONE
Proof
  rpt gen_tac >> PairCases_on `cf` >>
  simp[package_constructor_def, set_constructor_package_target_def,
    update_cenv_nonreentrant_def] >> rpt strip_tac >>
  gvs[] >> simp[build_compile_env_deploy_no_internal_return]
QED

Theorem ctor_checked_code_return_buf:
  !tops rpolicy runtime_bc dunit body cenv nr nkey ut imm exit_lbl sa sb sj
   st_exit st_epilogue st_final func.
  deploy_ctor_code tops rpolicy runtime_bc dunit
    (body,cenv,nr,nkey,ut,imm,exit_lbl,sa,sb,sj,st_exit,st_epilogue,st_final,func) ==>
  cenv.ce_return_buf = NONE
Proof
  rpt gen_tac >> simp[deploy_ctor_code_def] >> rpt strip_tac >>
  drule ctor_checked_package_return_buf >> strip_tac >>
  drule ctor_checked_registration_return_buf >> simp[]
QED

Theorem ctor_checked_entry_fields:
  !vs prog cplan tops es lbl func.
  gas_variant vs (deploy_entry_state prog cplan tops es) ==>
  (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>).vs_alloca_next = imm_len tops /\
  ~(vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>).vs_halted /\
  alloca_history func (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
Proof
  rpt gen_tac >> disch_tac >>
  `vs.vs_alloca_next = imm_len tops /\ ~vs.vs_halted /\ vs.vs_allocas = FEMPTY` by
    (fs[gas_variant_def, venom_state_component_equality] >>
     gvs[deploy_entry_state_def, entry_venom_state_def, init_venom_state_def]) >>
  simp[] >> irule alloca_history_empty >> simp[]
QED

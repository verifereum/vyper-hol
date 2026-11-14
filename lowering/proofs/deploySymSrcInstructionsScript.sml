Theory deploySymSrcInstructions
Ancestors
  deploySymSrcHistory deploySymSrcGenerate deploySymSrcConstructorArgs deploySymSrcConstructorSource
  deploySymSrcInternalBodies deploySymSrcGeneratorFrame runtimeSymSrcInstructions
  runtimeSymSrcContext runtimeSymSrcModuleArgPreservation runtimeSymSrcRuntimeBoundary
  runtimeSymSrcEmissionProbe compileVyper vyperCompiler moduleLowering compileEnv
  loweringShapeDefs context list

Theorem deploy_sym_run_lowering[local]:
  !has bytes len args size ints ce stmts pay nr key trans rp entry unit.
  (!s u s'. EVERY runtime_sym_inst (state_insts s) /\
    compile_generate_deploy has (LENGTH bytes) len args size ints ce stmts pay nr key trans s = (u,s') ==>
    EVERY deploy_sym_inst (state_insts s')) /\
  run_deploy_lowering has rp bytes len args size ints ce stmts pay nr key trans entry = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==> EVERY deploy_sym_inst (fn_insts fn)
Proof
  simp[run_deploy_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs(), install_immutable_reservation_def] >>
  `EVERY deploy_sym_inst (state_insts st1)` by metis_tac[runtime_sym_initial] >>
  drule_all runtime_sym_extract >> simp[]
QED

Theorem deploy_sym_deploy_insts:
  supported_program tops /\ supported_program_deploy tops /\
  ~program_reads_self_code tops /\
  lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit ==>
  !fn. MEM fn unit.cu_context.ctx_functions ==> EVERY deploy_sym_inst (fn_insts fn)
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `ctor_fn`
  >- (gvs[set_constructor_package_target_def] >>
      rpt gen_tac >> strip_tac >> irule deploy_sym_run_lowering >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      rpt gen_tac >>
      simp[compile_generate_deploy_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
      rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
      `EVERY deploy_sym_inst (state_insts s)` by
        metis_tac[EVERY_MEM, runtime_sym_inst_deploy] >>
      drule deploy_sym_simple_deploy >>
      disch_then (qspecl_then [`LENGTH runtime_bc`,
        `compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops`] mp_tac) >>
      simp[]) >>
  qpat_x_assum `(\(_,_,_,_,_,_,_,_). _) _ = _` mp_tac >>
  pairarg_tac >> simp[] >> strip_tac >>
  PairCases_on `x` >>
  `runtime_sym_env ctor_cenv /\
   ?bindings. supported_stmts tops bindings ctor_body /\
     ~supported_stmts_expr_exists is_self_code ctor_body /\
     (!ce'. runtime_sym_stmts_contract tops bindings compile_stmts ce' NoLoop NoneT ctor_body)` by
    (irule deploy_sym_constructor_package >>
     goal_assum (drule_at Any) >> simp[] >>
     qpat_x_assum `set_constructor_package_target _ _ = _` mp_tac >>
     simp[] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  rpt gen_tac >> strip_tac >> irule deploy_sym_run_lowering >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  rpt gen_tac >> strip_tac >>
  irule deploy_sym_generate_deploy_cond >>
  conj_tac >- metis_tac[deploy_sym_register_constructor_args] >>
  goal_assum (drule_at (Pat `compile_generate_deploy _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`bindings`,`tops`] >> simp[] >>
  `int_fns = FST (SND (classify_functions tops))` by simp[] >>
  pop_assum SUBST1_TAC >>
  rpt gen_tac >> strip_tac >>
  irule deploy_sym_classified_internal_bodies_cond >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  irule deploy_sym_internal_function >>
  conj_tac >- metis_tac[runtime_sym_alloc_buffer] >>
  conj_tac >- metis_tac[runtime_sym_fixed_region_with_id] >>
  goal_assum (drule_at (Pat `compile_internal_function _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at Any) >> simp[runtime_sym_stmts_closed] >>
  metis_tac[]
QED

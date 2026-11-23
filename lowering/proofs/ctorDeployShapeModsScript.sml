Theory ctorDeployShapeMods
Ancestors
  list pair compileUnit compileVyper compileEnv compileUnitPackageShape
  bodyFullShadowInternalCode
  ctorUnitShape deployUnitProducers loweringShapeProps loweringShapeSource
  loweringUnitEntryShape vyperCompiler vyperTypeContract unitShapeDefs
  o1PassContract venomInst

Theorem deploy_runner_source_shape[local]:
  run_deploy_lowering has rp bc imm args data_size ips ce ss pay nr key trans
    "__deploy" = SOME unit /\
  (has ==> cenv_static_mode_ok F ce /\ ce.ce_return_pc = NONE /\
           ~supported_stmts_expr_exists (expr_shape_root_mode F) ss) /\
  (~has ==> ips = []) /\
  EVERY (internal_fn_shape_mode_ok F) ips /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) ==>
  o1_source_unit_ok unit /\ unit_entry_no_params unit
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) unit.cu_context.ctx_functions)` by
    (drule run_deploy_lowering_context_ok >>
     simp[lowering_context_ok_def, ctx_fn_names_def]) >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors ips))` by
    (qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[run_deploy_lowering_def] >> pairarg_tac >> gvs[AllCaseEqs()] >>
     strip_tac >>
     gvs[install_immutable_reservation_def] >>
     drule extract_context_internal_names >> strip_tac >> fs[]) >>
  drule_all (Q.INST [`static` |-> `F`] run_deploy_lowering_source_unit_ok_mode) >>
  simp[] >> strip_tac >> irule unit_entry_no_params_from_first >> simp[]
QED

Theorem checked_lower_vyper_deploy_unit_source_shape_mods:
  lower_vyper_deploy_unit_mods mods exps rpolicy runtime_bc = SOME unit /\
  check_contract T layouts addr mods = SOME art ==>
  o1_source_unit_ok unit /\ unit_entry_no_params unit
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
  pure_rewrite_tac[lower_vyper_deploy_unit_mods_def, LET_THM] >> BETA_TAC >>
  pairarg_tac >> PURE_ASM_REWRITE_TAC[] >>
  CONV_TAC (DEPTH_CONV (BETA_CONV ORELSEC pairLib.PAIRED_BETA_CONV)) >>
  qmatch_goalsub_abbrev_tac `if reject then NONE else _` >>
  Cases_on `reject` >- simp[] >>
  qpat_x_assum `Abbrev _` kall_tac >> simp[] >>
  Cases_on `ctor_fn`
  >- (simp[set_constructor_package_target_def] >> strip_tac >>
      irule deploy_runner_source_shape >> first_assum (irule_at Any) >>
      simp[internal_fn_descriptors_def]) >>
  simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  irule deploy_runner_source_shape >> first_assum (irule_at Any) >> simp[] >>
  `EVERY (\nd. ~supported_exprs_exists (expr_shape_root_mode F) (SND nd))
      (build_func_defaults_mods mods)` by
    simp[EVERY_MEM, expr_shape_root_mode_dynamic, dynamic_raw_expr_shape] >>
  conj_tac
  >- (rename1 `package_constructor_unit _ _ _ cf` >> PairCases_on `cf` >>
      `cenv_static_mode_ok F
         (build_compile_env_unit mods NONE Deploy cf0 cf3 cf4 cf6 cf7 T) /\
       (build_compile_env_unit mods NONE Deploy cf0 cf3 cf4 cf6 cf7 T).ce_return_pc = NONE` by
        simp[Q.INST [`static` |-> `F`, `vis` |-> `Deploy`]
          build_compile_env_unit_static_mode] >>
      gvs[package_constructor_unit_def, set_constructor_package_target_def,
          update_cenv_nonreentrant_def, expr_shape_root_mode_dynamic,
          dynamic_raw_stmt_shape, cenv_static_mode_ok_def] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  qmatch_goalsub_abbrev_tac `internal_fn_descriptors pkgs` >>
  qpat_assum `Abbrev _`
    (assume_tac o PURE_REWRITE_RULE[markerTheory.Abbrev_def]) >>
  drule (Q.INST [`static` |-> `F`] package_internal_fn_unit_shape) >>
  (impl_tac
   >- (simp[EVERY_MEM, expr_shape_root_mode_dynamic, dynamic_raw_expr_shape] >>
       gen_tac >> rename1 `MEM f _ ==> _` >> PairCases_on `f` >>
       simp[dynamic_raw_stmt_shape])) >>
  strip_tac >> conj_tac >> first_assum ACCEPT_TAC
QED

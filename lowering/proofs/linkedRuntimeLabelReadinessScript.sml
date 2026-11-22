(* Raw runtime label checks for a linked compilation unit. *)
Theory linkedRuntimeLabelReadiness
Ancestors
  compileUnit compileUnitPackageShape runtimeLabelReadiness runtimeLabelRunners
  runtimeLabelInvariant runtimeLabelGenerators runtimeLabelExpr runtimeLabelStmt
  loweringShapeProps compileVyper compileEnv finite_map venomInst list pair

val _ = Parse.hide "body";

Theorem rb_build_compile_env_unit_for:
  rb_env_ok_for source_checks
    (build_compile_env_unit mods src vis mut fname args ret body use_trans)
Proof
  `!loc. static_loc loc ==> rb_location_ok_for source_checks loc` by
    (Cases >> simp[static_loc_def, rb_location_ok_for_def]) >>
  mp_tac build_compile_env_unit_static_locations >>
  simp[rb_env_ok_for_def] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  simp[build_compile_env_unit_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[AllCaseEqs(), allocate_internal_special_vars_def, rb_location_ok_for_def]
QED

Triviality rb_package_external_unit_for:
  rb_external_package_ok_for source_checks
    (set_external_package_target target (package_external_fn_unit mods trans keys f))
Proof
  PairCases_on `f` >>
  simp[package_external_fn_unit_def, set_external_package_target_def,
       rb_external_package_ok_for_def, rb_env_updates_for] >>
  Cases_on `f7 = NoneT` >> simp[rb_build_compile_env_unit_for] >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       rb_operand_ok_for_def, build_compile_env_unit_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Triviality rb_package_internal_unit_for:
  rb_internal_package_ok_for source_checks
    (set_internal_package_target target (package_internal_fn_unit mods trans keys F 0 f))
Proof
  PairCases_on `f` >>
  simp[package_internal_fn_unit_def, set_internal_package_target_def,
       rb_internal_package_ok_for_def, rb_build_compile_env_unit_for] >>
  simp[update_cenv_nonreentrant_def, rb_operand_ok_for_def,
       compileEnvTheory.internal_fn_label_def]
QED

Triviality rb_package_fallback_unit_for:
  rb_fallback_ok_for source_checks
    (set_fallback_package_target target (package_fallback_fn_unit mods trans keys f))
Proof
  Cases_on `f` >> simp[package_fallback_fn_unit_def,
    set_fallback_package_target_def, rb_fallback_ok_for_def] >>
  PairCases_on `x` >>
  simp[package_fallback_fn_unit_def, set_fallback_package_target_def,
       rb_fallback_ok_for_def, rb_env_updates_for] >>
  Cases_on `x7 = NoneT` >> simp[rb_build_compile_env_unit_for] >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       build_compile_env_unit_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Triviality rb_package_group_unit_for:
  rb_group_ok_for source_checks (package_external_group_unit mods target trans keys f)
Proof
  PairCases_on `f` >>
  `rb_external_package_ok_for source_checks (set_external_package_target target
      (package_external_fn_unit mods trans keys (f0,f1,f2,f3,f4,f5,f6,f7,f8)))` by
    simp[rb_package_external_unit_for] >>
  simp_tac std_ss [package_external_group_unit_def, LET_THM] >>
  IF_CASES_TAC
  >- gvs[compute_selector_def, rb_group_ok_for_def, rb_operand_ok_for_def] >>
  pairarg_tac >> gvs[] >>
  gvs[rb_group_ok_for_def, rb_external_package_ok_for_def,
      external_common_label_def, external_prefix_label_def,
      EVERY_MAP, FORALL_PROD, compute_selector_def, rb_operand_ok_for_def] >>
  simp[EVERY_MEM, FORALL_PROD]
QED

Theorem lower_vyper_runtime_unit_label_checks_mods:
  lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
  MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
  source_inst_ok source_checks inst
Proof
  strip_tac >>
  `rb_expr_contract_for source_checks` by simp[compile_expr_label_checks] >>
  `rb_stmt_contract_for source_checks` by simp[compile_stmts_label_checks] >>
  qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_mods_def] >>
  pairarg_tac >> simp[bool_case_eq] >> strip_tac >> gvs[]
  >- (drule_at (Pos (el 2)) rb_run_grouped_lowering_for >>
      disch_then (qspecl_then [`source_checks`, `fn`] mp_tac) >> impl_tac
      >- (simp[] >> irule compile_generate_grouped_runtime_label_checks >>
          simp[rb_grouped_runtime_inputs_ok_for_def, EVERY_MAP,
               rb_package_group_unit_for, rb_package_internal_unit_for,
               rb_package_fallback_unit_for]) >>
      simp[EVERY_MEM]) >>
  drule_at (Pos (el 2)) rb_run_lowering_for >>
  disch_then (qspecl_then [`source_checks`, `fn`] mp_tac) >> impl_tac
  >- (simp[] >> irule compile_generate_runtime_label_checks >>
      simp[rb_runtime_inputs_ok_for_def, EVERY_MAP, rb_build_selectors_for,
           rb_package_external_unit_for, rb_package_internal_unit_for,
           rb_package_fallback_unit_for]) >>
  simp[EVERY_MEM]
QED

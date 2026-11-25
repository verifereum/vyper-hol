(* Raw runtime instruction checks after generator and context extraction. *)
Theory runtimeLabelReadiness
Ancestors
  runtimeLabelStmtIO runtimeLabelPrimitives
  compileVyper vyperCompiler venomInst list runtimeLabelInvariant runtimeLabelValues
  runtimeLabelABI runtimeLabelBuiltins runtimeLabelExpr runtimeLabelStmt
  runtimeLabelGenerators entryExtractionCodePredicate entryCodePredicate loweringShapeDefs
  runtimeLabelRunners

Theorem rb_add_module_var_locations_for[local]:
  !tops vars. (!k loc. FLOOKUP vars k = SOME loc ==> (rb_location_ok_for source_checks) loc) ==>
    !k loc. FLOOKUP (add_module_var_locations tops vars) k = SOME loc ==>
      (rb_location_ok_for source_checks) loc
Proof
  Induct >> simp[add_module_var_locations_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum ho_match_mp_tac >>
  Cases_on `h` >> simp[add_module_var_locations_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  rpt gen_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  strip_tac >> gvs[rb_location_ok_for_def] >> first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem rb_add_immutable_locations_for[local]:
  !tops off vars. (!k loc. FLOOKUP vars k = SOME loc ==> (rb_location_ok_for source_checks) loc) ==>
    !k loc. FLOOKUP (add_immutable_locations sft tops off vars) k = SOME loc ==>
      (rb_location_ok_for source_checks) loc
Proof
  Induct >> simp[add_immutable_locations_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h` >> simp[add_immutable_locations_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >> first_x_assum ho_match_mp_tac >>
  rpt gen_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  strip_tac >> gvs[rb_location_ok_for_def] >> first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem rb_allocate_args_for[local]:
  allocate_args sft args off vars = (vars',off') /\
  (!k loc. FLOOKUP vars k = SOME loc ==> (rb_location_ok_for source_checks) loc) ==>
  !k loc. FLOOKUP vars' k = SOME loc ==> (rb_location_ok_for source_checks) loc
Proof
  rpt strip_tac >> Cases_on `MEM k (MAP FST args)`
  >- (drule_all allocate_args_FLOOKUP_arg >> strip_tac >> gvs[rb_location_ok_for_def]) >>
  drule_all allocate_args_FLOOKUP_other >> simp[] >> metis_tac[]
QED

Theorem rb_build_compile_env_for:
  !tops vis mut name args ret body trans.
    (rb_env_ok_for source_checks) (build_compile_env tops vis mut name args ret body trans)
Proof
  rpt gen_tac >> simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[rb_env_ok_for_def] >> rpt conj_tac
  >- (drule rb_allocate_args_for >> simp[] >> metis_tac[])
  >- (ho_match_mp_tac rb_add_immutable_locations_for >> ho_match_mp_tac rb_add_module_var_locations_for >> simp[]) >>
  gvs[AllCaseEqs(), allocate_internal_special_vars_def, rb_location_ok_for_def]
QED

Theorem rb_env_updates_for[simp]:
  ((rb_env_ok_for source_checks) (ce with ce_target := target) <=> (rb_env_ok_for source_checks) ce) /\
  ((rb_env_ok_for source_checks) (ce with ce_raw_return := rr) <=> (rb_env_ok_for source_checks) ce) /\
  ((rb_env_ok_for source_checks) (ce with ce_is_ctor := ctor) <=> (rb_env_ok_for source_checks) ce) /\
  ((rb_env_ok_for source_checks) (update_cenv_nonreentrant ce nr key trans view) <=> (rb_env_ok_for source_checks) ce) /\
  ((rb_env_ok_for source_checks) (update_cenv_ret_abi ce ret) <=> (rb_env_ok_for source_checks) ce)
Proof
  simp[rb_env_ok_for_def, update_cenv_nonreentrant_def, update_cenv_ret_abi_def]
QED

Theorem rb_build_compile_env_ctor[local]:
  !tops vis mut name args ret body trans.
    (build_compile_env tops vis mut name args ret body trans).ce_is_ctor =
      (vis = Deploy)
Proof
  rpt gen_tac >> simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem rb_package_external_for[local]:
  !tops trans keys f target.
    (rb_external_package_ok_for source_checks)
      (set_external_package_target target (package_external_fn tops trans keys f))
Proof
  rpt gen_tac >> PairCases_on `f` >>
  simp[package_external_fn_def, set_external_package_target_def,
       rb_external_package_ok_for_def, rb_env_updates_for] >>
  Cases_on `f6 = NoneT` >>
  simp[rb_build_compile_env_for] >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       rb_build_compile_env_ctor, rb_operand_ok_for_def]
QED

Theorem rb_package_internal_for[local]:
  !tops trans keys f target.
    (rb_internal_package_ok_for source_checks)
      (set_internal_package_target target (package_internal_fn tops trans keys F 0 f))
Proof
  rpt gen_tac >> PairCases_on `f` >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       rb_internal_package_ok_for_def, rb_build_compile_env_for] >>
  simp[update_cenv_nonreentrant_def, rb_build_compile_env_ctor,
       rb_operand_ok_for_def, compileEnvTheory.internal_fn_label_def]
QED

Theorem rb_package_fallback_for[local]:
  !tops trans keys f target.
    (rb_fallback_ok_for source_checks)
      (set_fallback_package_target target (package_fallback_fn tops trans keys f))
Proof
  rpt gen_tac >> Cases_on `f` >> simp[package_fallback_fn_def,
    set_fallback_package_target_def, rb_fallback_ok_for_def] >> PairCases_on `x` >>
  simp[package_fallback_fn_def, set_fallback_package_target_def,
       rb_fallback_ok_for_def, rb_env_updates_for] >>
  Cases_on `x6 = NoneT` >> simp[rb_build_compile_env_for] >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       rb_build_compile_env_ctor]
QED

Theorem rb_package_group_for[local]:
  !tops target trans keys f.
    (rb_group_ok_for source_checks) (package_external_group tops target trans keys f)
Proof
  rpt gen_tac >> PairCases_on `f` >>
  `(rb_external_package_ok_for source_checks) (set_external_package_target target
    (package_external_fn tops trans keys (f0,f1,f2,f3,f4,f5,f6,f7)))` by
    simp[rb_package_external_for] >>
  simp_tac std_ss [package_external_group_def, LET_THM] >>
  IF_CASES_TAC
  >- gvs[compute_selector_def, rb_group_ok_for_def, rb_operand_ok_for_def] >>
  pairarg_tac >> gvs[] >>
  gvs[rb_group_ok_for_def, rb_external_package_ok_for_def,
      external_common_label_def, external_prefix_label_def,
      EVERY_MAP, pairTheory.FORALL_PROD, compute_selector_def,
      rb_operand_ok_for_def] >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD]
QED

Theorem lower_vyper_runtime_unit_label_checks:
  !tops rpolicy unit fn inst.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    source_inst_ok source_checks inst
Proof
  rpt gen_tac >> strip_tac >>
  `(rb_expr_contract_for source_checks)` by simp[compile_expr_label_checks] >>
  `(rb_stmt_contract_for source_checks)` by metis_tac[compile_stmts_label_checks] >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp_tac std_ss [lower_vyper_runtime_unit_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac std_ss [LET_THM] >>
  IF_CASES_TAC >> simp[] >> strip_tac
  >- (drule_at (Pos (el 2)) rb_run_grouped_lowering_for >>
      disch_then (qspecl_then [`source_checks`, `fn`] mp_tac) >> impl_tac
      >- (simp[] >> irule compile_generate_grouped_runtime_label_checks >>
          simp[rb_grouped_runtime_inputs_ok_for_def, EVERY_MAP,
               rb_package_group_for, rb_package_internal_for, rb_package_fallback_for]) >>
      simp[EVERY_MEM]) >>
  drule_at (Pos (el 2)) rb_run_lowering_for >>
  disch_then (qspecl_then [`source_checks`, `fn`] mp_tac) >> impl_tac
  >- (simp[] >> irule compile_generate_runtime_label_checks >>
      simp[rb_runtime_inputs_ok_for_def, EVERY_MAP, rb_build_selectors_for,
           rb_package_external_for, rb_package_internal_for, rb_package_fallback_for]) >>
  simp[EVERY_MEM]
QED

(* The runtime-begin exclusions use the original checks. *)

Theorem lower_vyper_runtime_unit_no_runtime_begin:
  !tops rpolicy unit fn inst.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`source_checks` |-> `({"runtime_begin"}, F)`]
    lower_vyper_runtime_unit_label_checks) >>
  simp[EVERY_MEM, source_inst_ok_def, rb_operand_ok_legacy, rb_operand_ok_def] >>
  metis_tac[]
QED

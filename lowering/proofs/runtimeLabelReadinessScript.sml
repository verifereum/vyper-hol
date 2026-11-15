(* Runtime lowering cannot emit the constructor's runtime data symbol.
   Runtime packages use ordinary locations; generated branch and function
   labels occupy disjoint prefixed namespaces. *)
Theory runtimeLabelReadiness
Ancestors
  runtimeLabelStmtIO runtimeLabelPrimitives
  compileVyper vyperCompiler venomInst list runtimeLabelInvariant runtimeLabelValues
  runtimeLabelABI runtimeLabelBuiltins runtimeLabelExpr runtimeLabelStmt
  runtimeLabelGenerators entryExtractionCodePredicate entryCodePredicate loweringShapeDefs

Theorem rb_state_entry_code[local]:
  rb_state_ok st <=> entry_code_pred (\i. EVERY rb_operand_ok i.inst_operands) st
Proof
  simp[rb_state_ok_def, state_insts_def, all_blocks_def,
       entry_code_pred_def, EVERY_FLAT, EVERY_MAP] >> metis_tac[]
QED

Theorem rb_extract_context[local]:
  rb_state_ok st /\
  extract_context_with_internals entry internals st = SOME (ctx,data) /\
  MEM fn ctx.ctx_functions ==>
  EVERY (\i. EVERY rb_operand_ok i.inst_operands) (fn_insts fn)
Proof
  simp[rb_state_entry_code] >> strip_tac >>
  drule_all entry_code_extracted_context >> simp[]
QED

Theorem rb_run_lowering[local]:
  rb_step (K T) (compile_generate_runtime sels exts ints fb
    rp.rpol_frontend_dispatch bc width buckets info) /\
  run_lowering sels exts ints fb rp bc width buckets info entry = SOME unit /\
  MEM fn unit.cu_context.ctx_functions ==>
  EVERY (\i. EVERY rb_operand_ok i.inst_operands) (fn_insts fn)
Proof
  simp[run_lowering_def] >> strip_tac >> pairarg_tac >>
  gvs[AllCaseEqs()] >>
  `rb_state_ok st1` by
    (qpat_x_assum `rb_step _ _` mp_tac >>
     simp[rb_step_def] >> disch_then (qspec_then `initial_compile_state entry` mp_tac) >>
     simp[rb_state_ok_def, state_insts_def, all_blocks_def, initial_compile_state_def]) >>
  drule_at (Pos (el 2)) rb_extract_context >> disch_then drule_all >> simp[]
QED

Theorem rb_run_grouped_lowering[local]:
  rb_step (K T) (compile_generate_grouped_runtime groups ints fb) /\
  run_grouped_lowering groups ints fb rp entry = SOME unit /\
  MEM fn unit.cu_context.ctx_functions ==>
  EVERY (\i. EVERY rb_operand_ok i.inst_operands) (fn_insts fn)
Proof
  simp[run_grouped_lowering_def] >> strip_tac >> pairarg_tac >>
  gvs[AllCaseEqs()] >>
  `rb_state_ok st1` by
    (qpat_x_assum `rb_step _ _` mp_tac >>
     simp[rb_step_def] >> disch_then (qspec_then `initial_compile_state entry` mp_tac) >>
     simp[rb_state_ok_def, state_insts_def, all_blocks_def, initial_compile_state_def]) >>
  drule_at (Pos (el 2)) rb_extract_context >> disch_then drule_all >> simp[]
QED

Theorem rb_add_module_var_locations[local]:
  !tops vars. (!k loc. FLOOKUP vars k = SOME loc ==> rb_location_ok loc) ==>
    !k loc. FLOOKUP (add_module_var_locations tops vars) k = SOME loc ==>
      rb_location_ok loc
Proof
  Induct >> simp[add_module_var_locations_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum ho_match_mp_tac >>
  Cases_on `h` >> simp[add_module_var_locations_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  rpt gen_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  strip_tac >> gvs[rb_location_ok_def] >> first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem rb_add_immutable_locations[local]:
  !tops off vars. (!k loc. FLOOKUP vars k = SOME loc ==> rb_location_ok loc) ==>
    !k loc. FLOOKUP (add_immutable_locations sft tops off vars) k = SOME loc ==>
      rb_location_ok loc
Proof
  Induct >> simp[add_immutable_locations_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h` >> simp[add_immutable_locations_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >> first_x_assum ho_match_mp_tac >>
  rpt gen_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[]) >>
  strip_tac >> gvs[rb_location_ok_def] >> first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem rb_allocate_args[local]:
  allocate_args sft args off vars = (vars',off') /\
  (!k loc. FLOOKUP vars k = SOME loc ==> rb_location_ok loc) ==>
  !k loc. FLOOKUP vars' k = SOME loc ==> rb_location_ok loc
Proof
  rpt strip_tac >> Cases_on `MEM k (MAP FST args)`
  >- (drule_all allocate_args_FLOOKUP_arg >> strip_tac >> gvs[rb_location_ok_def]) >>
  drule_all allocate_args_FLOOKUP_other >> simp[] >> metis_tac[]
QED

Theorem rb_build_compile_env[local]:
  !tops vis mut name args ret body trans.
    rb_env_ok (build_compile_env tops vis mut name args ret body trans)
Proof
  rpt gen_tac >> simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[]) >>
  simp[rb_env_ok_def] >> rpt conj_tac
  >- (drule rb_allocate_args >> simp[])
  >- (ho_match_mp_tac rb_add_immutable_locations >> ho_match_mp_tac rb_add_module_var_locations >> simp[]) >>
  gvs[AllCaseEqs(), allocate_internal_special_vars_def, rb_location_ok_def]
QED

Theorem rb_env_updates[local,simp]:
  (rb_env_ok (ce with ce_target := target) <=> rb_env_ok ce) /\
  (rb_env_ok (ce with ce_raw_return := rr) <=> rb_env_ok ce) /\
  (rb_env_ok (ce with ce_is_ctor := ctor) <=> rb_env_ok ce) /\
  (rb_env_ok (update_cenv_nonreentrant ce nr key trans view) <=> rb_env_ok ce) /\
  (rb_env_ok (update_cenv_ret_abi ce ret) <=> rb_env_ok ce)
Proof
  simp[rb_env_ok_def, update_cenv_nonreentrant_def, update_cenv_ret_abi_def]
QED

Theorem rb_build_compile_env_ctor[local]:
  !tops vis mut name args ret body trans.
    (build_compile_env tops vis mut name args ret body trans).ce_is_ctor =
      (vis = Deploy)
Proof
  rpt gen_tac >> simp[build_compile_env_def] >> rpt (pairarg_tac >> gvs[])
QED

Theorem rb_package_external[local]:
  !tops trans keys f target.
    rb_external_package_ok
      (set_external_package_target target (package_external_fn tops trans keys f))
Proof
  rpt gen_tac >> PairCases_on `f` >>
  simp[package_external_fn_def, set_external_package_target_def,
       rb_external_package_ok_def, rb_env_updates] >>
  Cases_on `f6 = NoneT` >>
  simp[rb_build_compile_env] >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       rb_build_compile_env_ctor, rb_operand_ok_def]
QED

Theorem rb_package_internal[local]:
  !tops trans keys f target.
    rb_internal_package_ok
      (set_internal_package_target target (package_internal_fn tops trans keys F 0 f))
Proof
  rpt gen_tac >> PairCases_on `f` >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       rb_internal_package_ok_def, rb_build_compile_env] >>
  simp[update_cenv_nonreentrant_def, rb_build_compile_env_ctor,
       rb_operand_ok_def, compileEnvTheory.internal_fn_label_def]
QED

Theorem rb_package_fallback[local]:
  !tops trans keys f target.
    rb_fallback_ok
      (set_fallback_package_target target (package_fallback_fn tops trans keys f))
Proof
  rpt gen_tac >> Cases_on `f` >> simp[package_fallback_fn_def,
    set_fallback_package_target_def, rb_fallback_ok_def] >> PairCases_on `x` >>
  simp[package_fallback_fn_def, set_fallback_package_target_def,
       rb_fallback_ok_def, rb_env_updates] >>
  Cases_on `x6 = NoneT` >> simp[rb_build_compile_env] >>
  simp[update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       rb_build_compile_env_ctor]
QED

Theorem rb_build_selectors[local]:
  !fs. EVERY (\(sel,lbl,tz). rb_operand_ok (Label lbl)) (build_selectors tenv fs)
Proof
  Induct >> simp[build_selectors_def] >> gen_tac >> PairCases_on `h` >>
  gvs[build_selectors_def, compute_selector_def, rb_operand_ok_def]
QED

Theorem rb_package_group[local]:
  !tops target trans keys f.
    rb_group_ok (package_external_group tops target trans keys f)
Proof
  rpt gen_tac >> PairCases_on `f` >>
  `rb_external_package_ok (set_external_package_target target
    (package_external_fn tops' trans keys (f0,f1,f2,f3,f4,f5,f6,f7)))` by
    simp[rb_package_external] >>
  simp_tac std_ss [package_external_group_def, LET_THM] >>
  IF_CASES_TAC
  >- gvs[compute_selector_def, rb_group_ok_def, rb_operand_ok_def] >>
  pairarg_tac >> gvs[] >>
  gvs[rb_group_ok_def, rb_external_package_ok_def,
      external_common_label_def, external_prefix_label_def,
      EVERY_MAP, pairTheory.FORALL_PROD, compute_selector_def,
      rb_operand_ok_def] >>
  simp[EVERY_MEM, pairTheory.FORALL_PROD]
QED

Theorem lower_vyper_runtime_unit_no_runtime_begin:
  !tops rpolicy unit fn inst.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "runtime_begin") inst.inst_operands
Proof
  rpt gen_tac >> strip_tac >>
  `rb_expr_contract` by simp[compile_expr_no_runtime_begin] >>
  `rb_stmt_contract` by metis_tac[compile_stmts_no_runtime_begin] >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp_tac std_ss [lower_vyper_runtime_unit_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac std_ss [LET_THM] >>
  IF_CASES_TAC >> simp[] >> strip_tac
  >- (drule_at (Pos (el 2)) rb_run_grouped_lowering >>
      disch_then (qspec_then `fn` mp_tac) >> impl_tac
      >- (simp[] >> irule compile_generate_grouped_runtime_no_runtime_begin >>
          simp[rb_grouped_runtime_inputs_ok_def, EVERY_MAP,
               rb_package_group, rb_package_internal, rb_package_fallback]) >>
      simp[EVERY_MEM, rb_operand_ok_def] >> metis_tac[]) >>
  drule_at (Pos (el 2)) rb_run_lowering >>
  disch_then (qspec_then `fn` mp_tac) >> impl_tac
  >- (simp[] >> irule compile_generate_runtime_no_runtime_begin >>
      simp[rb_runtime_inputs_ok_def, EVERY_MAP, rb_build_selectors,
           rb_package_external, rb_package_internal, rb_package_fallback]) >>
  simp[EVERY_MEM, rb_operand_ok_def] >> metis_tac[]
QED

(* Source shape and reservation facts for deploy_unit_o1_shape_ok.
 * Static lowering proves its shape directly. The three dynamic forms use
 * their source-shape certificates. The O1 passes preserve the reservation,
 * and the generated context plan checks that it is well formed.
 *)
Theory ctorDeployShape
Ancestors
  list ctorDeployDefs immSectionDead o1PassContract unitShapeDefs staticLayoutDefs
  ctorUnitShape deployUnitProducers loweringShapeProps loweringShapeSource
  loweringUnitEntryShape
  supportedProgram supportedNames compileVyper vyperCompiler
  o1PipelineCorrect o1ComposeSupport fcgPruning stackPlanGen
  venomPipelineRunner venomFnScheduleRunner venomFnScheduleRunnerProps
  ctorGeneratorShape loweringShapeDefs moduleLowering compileEnv context
  whitelistCheckerDeploy
  emitHelper venomInst ptrDiscipline deployDynamicMemory
  e2eDeployDefs vyperTypeContract constSubst supportedStmtTraverse supportedExprTraverse alist

(* ===== The constructor's source ===== *)

Theorem build_compile_env_non_internal_no_return_pc[local]:
  !tops vis mut fname args ret body use_trans.
    vis <> Internal ==>
    (build_compile_env tops vis mut fname args ret body use_trans).ce_return_pc =
      NONE
Proof
  rpt strip_tac >> simp[build_compile_env_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem deploy_classified_body_mode[local]:
  !layouts addr tops art mut nr rr name args dflts ret body.
    check_contract T layouts addr [(NONE,tops)] = SOME art /\
    ~deploy_dalloca_form_occurs (expr_raw_shape_root_mode static) tops /\
    IS_SOME (SND (SND (SND (classify_functions tops)))) /\
    (MEM (mut,nr,rr,name,args,dflts,ret,body) (FST (SND (classify_functions tops))) \/
     SND (SND (SND (classify_functions tops))) =
       SOME (mut,nr,rr,name,args,dflts,ret,body)) ==>
    ~supported_stmts_expr_exists (expr_shape_root_mode static) body /\
    ~supported_exprs_exists (expr_shape_root_mode static) dflts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!id r. ALOOKUP (module_consts_env tops []) id = SOME r ==>
     ~supported_expr_exists (expr_shape_root_mode static) r` by
    metis_tac[checked_module_consts_env_replacement_shape_mode, ALOOKUP_def] >>
  `!v m n r nm a ds ty b.
    MEM (FunctionDecl v m n r nm a ds ty b) tops /\
    (v = Deploy \/ v = Internal) ==>
    ~supported_stmts_expr_exists (expr_shape_root_mode static) b /\
    ~supported_exprs_exists (expr_shape_root_mode static) ds` by
    (rpt gen_tac >> strip_tac >>
     `~supported_stmts_expr_exists (expr_raw_shape_root_mode static) b /\
      ~supported_exprs_exists (expr_raw_shape_root_mode static) ds` by
       (fs[deploy_dalloca_form_occurs_def, supported_exprs_exists_every,
           EVERY_MEM, EXISTS_MEM] >> metis_tac[]) >>
     metis_tac[checked_deploy_function_raw_shape_mode]) >>
  qpat_x_assum `MEM _ _ \/ _ = SOME _` strip_assume_tac
  >- (gvs[MEM_classify_internal, subst_consts_fn_def] >>
      conj_tac
      >- (irule (cj 2 subst_consts_stmt_shape_mode) >> simp[] >> metis_tac[]) >>
      irule (cj 3 subst_consts_expr_shape_mode) >> simp[] >> metis_tac[]) >>
  drule classify_functions_ctor_mem >> strip_tac >>
  gvs[subst_consts_fn_def] >>
  conj_tac
  >- (irule (cj 2 subst_consts_stmt_shape_mode) >> simp[] >> metis_tac[]) >>
  irule (cj 3 subst_consts_expr_shape_mode) >> simp[] >> metis_tac[]
QED

Theorem deploy_classified_defaults_mode[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art /\
  ~deploy_dalloca_form_occurs (expr_raw_shape_root_mode static) tops /\
  IS_SOME (SND (SND (SND (classify_functions tops)))) ==>
  EVERY (\nd. ~supported_exprs_exists (expr_shape_root_mode static) (SND nd))
    (build_func_defaults tops)
Proof
  rw[build_func_defaults_def, EVERY_MEM] >>
  gvs[MEM_MAP] >> PairCases_on `y` >> gvs[] >>
  metis_tac[deploy_classified_body_mode]
QED

Theorem package_constructor_shape_ok_mode[local]:
  !tops layouts addr art use_trans nkey_map target cf cenv args pay nr nkey trans body ret.
    check_contract T layouts addr [(NONE,tops)] = SOME art /\
    ~deploy_dalloca_form_occurs (expr_raw_shape_root_mode static) tops /\
    SND (SND (SND (classify_functions tops))) = SOME cf /\
    set_constructor_package_target target
      (package_constructor tops use_trans nkey_map cf) =
      (cenv, args, pay, nr, nkey, trans, body, ret) ==>
    cenv_static_mode_ok static cenv /\ cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists (expr_shape_root_mode static) body
Proof
  rpt gen_tac >> PairCases_on `cf` >> strip_tac >>
  `IS_SOME (SND (SND (SND (classify_functions tops))))` by simp[] >>
  drule_all deploy_classified_defaults_mode >> strip_tac >>
  `~supported_stmts_expr_exists (expr_shape_root_mode static) cf7` by
    metis_tac[deploy_classified_body_mode] >>
  gvs[package_constructor_def, set_constructor_package_target_def,
      update_cenv_nonreentrant_def, build_compile_env_non_internal_no_return_pc] >>
  simp[cenv_static_mode_ok_def] >>
  metis_tac[build_compile_env_static_mode, cenv_static_mode_ok_def]
QED

Theorem package_internal_fn_ctor_shape_ok_mode[local]:
  !tops layouts addr art use_trans nkey_map imm target src.
    check_contract T layouts addr [(NONE,tops)] = SOME art /\
    ~deploy_dalloca_form_occurs (expr_raw_shape_root_mode static) tops /\
    IS_SOME (SND (SND (SND (classify_functions tops)))) /\
    MEM src (FST (SND (classify_functions tops))) ==>
    internal_fn_shape_mode_ok static
      (set_internal_package_target target
         (package_internal_fn tops use_trans nkey_map T imm src))
Proof
  rpt gen_tac >> PairCases_on `src` >> strip_tac >>
  drule_all deploy_classified_defaults_mode >> strip_tac >>
  `~supported_stmts_expr_exists (expr_shape_root_mode static) src7` by
    metis_tac[deploy_classified_body_mode] >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       update_cenv_nonreentrant_def, internal_fn_shape_mode_ok_def,
       cenv_static_mode_ok_def] >>
  metis_tac[build_compile_env_static_mode, cenv_static_mode_ok_def]
QED

Theorem package_constructor_shape_ok_static:
  !tops layouts (addr:160 word) art use_trans nkey_map target cf cenv args pay nr nkey trans body ret.
    check_contract T layouts addr [(NONE,tops)] = SOME art /\
    ~deploy_dalloca_form_occurs expr_raw_shape_root tops /\
    SND (SND (SND (classify_functions tops))) = SOME cf /\
    set_constructor_package_target target
      (package_constructor tops use_trans nkey_map cf) =
      (cenv, args, pay, nr, nkey, trans, body, ret) ==>
    cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root body
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss())
    [expr_raw_shape_root_mode_static, cenv_static_mode_ok_static,
     expr_shape_root_mode_static]
    (Q.INST [`static` |-> `T`] package_constructor_shape_ok_mode)) >>
  simp[]
QED

Theorem package_internal_fn_ctor_shape_ok_static:
  !tops layouts (addr:160 word) art use_trans nkey_map imm target src.
    check_contract T layouts addr [(NONE,tops)] = SOME art /\
    ~deploy_dalloca_form_occurs expr_raw_shape_root tops /\
    IS_SOME (SND (SND (SND (classify_functions tops)))) /\
    MEM src (FST (SND (classify_functions tops))) ==>
    internal_fn_shape_ok
      (set_internal_package_target target
         (package_internal_fn tops use_trans nkey_map T imm src))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all (SIMP_RULE (srw_ss())
    [expr_raw_shape_root_mode_static, internal_fn_shape_mode_ok_static]
    (Q.INST [`static` |-> `T`] package_internal_fn_ctor_shape_ok_mode)) >>
  simp[]
QED

(* ===== The lowered unit ===== *)

(* The entry function of run_deploy_lowering is the generator's entry
   blocks, whose instructions are entry code (lowered_inst_ok F): no PARAM.
   The prefix is run_deploy_lowering_source_unit_ok's. *)
Theorem run_deploy_lowering_entry_no_params[local]:
  !has_constructor rpolicy runtime_bytecode immutables_len constructor_args
   data_size ctor_internal_fns cenv body is_payable is_nonreentrant nkey
   use_transient unit.
    run_deploy_lowering has_constructor rpolicy runtime_bytecode immutables_len
      constructor_args data_size ctor_internal_fns cenv body is_payable
      is_nonreentrant nkey use_transient "__deploy" = SOME unit /\
    (has_constructor ==>
      cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
      ~supported_stmts_expr_exists expr_shape_root body) /\
    (~has_constructor ==> ctor_internal_fns = []) /\
    EVERY internal_fn_shape_ok ctor_internal_fns /\
    EVERY (\d. internal_label_ok (FST d))
      (internal_fn_descriptors ctor_internal_fns) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors ctor_internal_fns)) ==>
    EVERY (\inst. ~is_param_opcode inst.inst_opcode)
      (fn_insts (HD unit.cu_context.ctx_functions))
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `~supported_stmts_expr_exists expr_shape_root ss` >>
  `(if has_constructor then ctor_internal_fns else []) = ctor_internal_fns`
    by (Cases_on `has_constructor` >> gvs[]) >>
  Cases_on `compile_generate_deploy has_constructor (LENGTH runtime_bytecode)
    immutables_len constructor_args data_size ctor_internal_fns cenv ss
    is_payable is_nonreentrant nkey use_transient
    (initial_compile_state "__deploy")` >>
  rename1 `_ = (u, st1)` >> Cases_on `u` >>
  drule compile_generate_deploy_shape >> simp[] >> strip_tac >>
  drule_all shape_state_source_certificates >> strip_tac >>
  `package_internal_blocks (internal_fn_descriptors ctor_internal_fns)
     (entry_blocks ++ FLAT segs) =
   SOME (entry_blocks,
         MAP2 (\d seg. mk_internal_function (FST d) seg (FST (SND d))
                         (SND (SND d))) (internal_fn_descriptors ctor_internal_fns)
              segs)`
    by (irule package_internal_blocks_segments >> asm_rewrite_tac [] >>
        REWRITE_TAC[EVERY_MEM] >> gen_tac >> strip_tac >> BETA_TAC >>
        irule deploy_internal_label_separate >> fs[EVERY_MEM]) >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `all_blocks st1 = _`
    (assume_tac o REWRITE_RULE[all_blocks_def]) >>
  gs[run_deploy_lowering_def, extract_context_with_internals_def] >>
  strip_tac >> gvs[install_immutable_reservation_def, mk_venom_context_def] >>
  simp[fn_insts_def, mk_raw_function_def, EVERY_MEM,
       MEM_fn_insts_blocks_iff, PULL_EXISTS] >>
  rpt strip_tac >> gvs[EVERY_MEM] >> res_tac >>
  gvs[lowered_inst_ok_def]
QED

Theorem checked_deploy_internal_function_names[local]:
  check_contract T layouts addr [(NONE,tops)] = SOME art ==>
  ALL_DISTINCT (supported_internal_function_names tops)
Proof
  strip_tac >>
  drule (Q.INST [`vis` |-> `Internal`]
    check_contract_deploy_function_names_same_vis_distinct) >>
  `!ts. supported_internal_function_names ts =
        supported_function_names
          (FILTER (\t. ?m nr rr n a d r b.
                     t = FunctionDecl Internal m nr rr n a d r b) ts)`
    suffices_by simp[] >>
  Induct >> simp[supported_internal_function_names_def,
                 supported_function_names_def] >>
  Cases >> simp[supported_function_names_def] >> rw[] >>
  gvs[supported_function_names_def] >>
  rename1 `vis <> Internal` >> Cases_on `vis` >> gvs[]
QED

Theorem lower_vyper_deploy_unit_run_mode[local]:
  !tops rpolicy runtime_bc unit layouts addr art.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit /\
    check_contract T layouts addr [(NONE,tops)] = SOME art /\
    ~deploy_dalloca_form_occurs (expr_raw_shape_root_mode static) tops ==>
    ?has_constructor imm args ctor_internal_fns cenv body pay nr nkey trans.
      run_deploy_lowering has_constructor rpolicy runtime_bc imm args 0
        ctor_internal_fns cenv body pay nr nkey trans "__deploy" = SOME unit /\
      (has_constructor ==>
        cenv_static_mode_ok static cenv /\ cenv.ce_return_pc = NONE /\
        ~supported_stmts_expr_exists (expr_shape_root_mode static) body) /\
      (~has_constructor ==> ctor_internal_fns = []) /\
      EVERY (internal_fn_shape_mode_ok static) ctor_internal_fns /\
      EVERY (\d. internal_label_ok (FST d))
        (internal_fn_descriptors ctor_internal_fns) /\
      ALL_DISTINCT (MAP FST (internal_fn_descriptors ctor_internal_fns))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_vyper_deploy_unit _ _ _ = _` mp_tac >>
  simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  first_x_assum (irule_at Any) >>
  Cases_on `ctor_fn` >> gvs[internal_fn_descriptors_def] >>
  rename1 `classify_functions tops = (ext_fns, int_fns, fb_fn, SOME cf)` >>
  `SND (SND (SND (classify_functions tops))) = SOME cf` by simp[] >>
  drule_all package_constructor_shape_ok_mode >> strip_tac >> simp[] >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
                   (FST (SND (classify_functions tops))))`
    by metis_tac[classified_internal_names_distinct,
                 checked_deploy_internal_function_names] >>
  qspecl_then [`tops`, `T`] mp_tac internal_descriptors_ok >>
  impl_tac >- simp[] >> simp[] >> strip_tac >>
  `ALL_DISTINCT (MAP FST (MAP (source_internal_fn_descriptor tops T)
     (order_internals (deploy_internal_order (SOME cf) int_fns) int_fns)))`
    by (REWRITE_TAC [listTheory.MAP_MAP_o] >>
        irule ALL_DISTINCT_order_deploy_internals >> fs[listTheory.MAP_MAP_o]) >>
  gs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
     internal_fn_descriptors_MAP_package_internal_fn, EVERY_MAP] >>
  simp[EVERY_MEM] >> rpt strip_tac
  >- (irule package_internal_fn_ctor_shape_ok_mode >>
      gs[] >> qexistsl_tac [`addr`, `art`, `layouts`] >>
      first_assum ACCEPT_TAC) >>
  fs[EVERY_MEM]
QED

Theorem lower_vyper_deploy_unit_run_static[local]:
  !tops rpolicy runtime_bc unit am tx.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit /\
    deploy_source_ok tops am tx /\
    ~deploy_dalloca_form_occurs expr_raw_shape_root tops ==>
    ?has_constructor imm args ctor_internal_fns cenv body pay nr nkey trans.
      run_deploy_lowering has_constructor rpolicy runtime_bc imm args 0
        ctor_internal_fns cenv body pay nr nkey trans "__deploy" = SOME unit /\
      (has_constructor ==>
        cenv_static_ok cenv /\ cenv.ce_return_pc = NONE /\
        ~supported_stmts_expr_exists expr_shape_root body) /\
      (~has_constructor ==> ctor_internal_fns = []) /\
      EVERY internal_fn_shape_ok ctor_internal_fns /\
      EVERY (\d. internal_label_ok (FST d))
        (internal_fn_descriptors ctor_internal_fns) /\
      ALL_DISTINCT (MAP FST (internal_fn_descriptors ctor_internal_fns))
Proof
  rpt gen_tac >> strip_tac >>
  `?art. check_contract T am.layouts tx.target [(NONE,tops)] = SOME art` by
    fs[deploy_source_ok_def, deploy_typing_ok_def] >>
  drule_all (SIMP_RULE (srw_ss())
    [expr_raw_shape_root_mode_static, cenv_static_mode_ok_static,
     expr_shape_root_mode_static, internal_fn_shape_mode_ok_static]
    (Q.INST [`static` |-> `T`] lower_vyper_deploy_unit_run_mode)) >>
  simp[]
QED

Theorem lower_vyper_deploy_unit_no_dalloca_static:
  !tops rpolicy runtime_bc unit am tx.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit /\
    deploy_source_ok tops am tx /\
    ~deploy_dalloca_form_occurs expr_raw_shape_root tops ==>
    ~ctx_has_dalloca unit.cu_context
Proof
  rpt gen_tac >> strip_tac >> irule every_no_dalloca >>
  drule_all lower_vyper_deploy_unit_run_static >> strip_tac >>
  drule run_deploy_lowering_source_unit_ok >> impl_tac >- simp[] >> simp[]
QED

Theorem deploy_unit_no_dalloca_static:
  deploy_phases policy tops (deploy_bc, runtime_bc)
    (rpolicy, dunit, dout, prog, cplan) /\
  deploy_source_ok tops am tx /\
  ~deploy_dalloca_form_occurs expr_raw_shape_root tops ==>
  ~ctx_has_dalloca dunit.cu_context
Proof
  simp[deploy_phases_def] >> metis_tac[lower_vyper_deploy_unit_no_dalloca_static]
QED

Theorem run_deploy_lowering_raw_defaults[local]:
  run_deploy_lowering has_constructor rpolicy runtime_bc immutables_len
    constructor_args data_size ctor_internal_fns cenv stmts is_payable
    is_nonreentrant nkey use_transient entry_label = SOME u ==>
  EVERY (\fn. fn.fn_eom = NONE) u.cu_context.ctx_functions /\
  unit_fmp_unsealed u
Proof
  simp[run_deploy_lowering_def, extract_context_with_internals_def,
       install_immutable_reservation_def, mk_venom_context_def,
       unit_fmp_unsealed_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_raw_function_def] >>
  drule package_internal_blocks_raw_defaults >>
  simp[EVERY_MEM, function_raw_metadata_defaults_def]
QED

Theorem lower_vyper_deploy_unit_eom_none:
  !tops rpolicy runtime_bc unit.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit ==>
    EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
    unit_fmp_unsealed unit
Proof
  rpt gen_tac >> simp[lower_vyper_deploy_unit_def] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> rpt strip_tac >>
  drule run_deploy_lowering_raw_defaults >> simp[]
QED

Theorem lower_vyper_deploy_unit_o1_shape_extras_static[local]:
  !tops rpolicy runtime_bc unit am tx.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit /\
    deploy_source_ok tops am tx /\
    ~deploy_dalloca_form_occurs expr_raw_shape_root tops ==>
    o1_source_unit_ok unit /\ unit_entry_no_params unit
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lower_vyper_deploy_unit_run_static >> strip_tac >>
  drule_all run_deploy_lowering_entry_no_params >> strip_tac >>
  drule_all run_deploy_lowering_source_unit_ok >> strip_tac >> simp[] >>
  irule unit_entry_no_params_from_first >> simp[] >>
  drule lower_vyper_deploy_unit_context_ok >>
  simp[lowering_context_ok_def, ctx_fn_names_def]
QED

Theorem lower_vyper_deploy_unit_dynamic_source_unit_shape[local]:
  !tops rpolicy runtime_bc unit layouts addr art.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME unit /\
    check_contract T layouts addr [(NONE,tops)] = SOME art ==>
    o1_source_unit_ok unit /\ unit_entry_no_params unit
Proof
  rpt gen_tac >> strip_tac >>
  `~deploy_dalloca_form_occurs (expr_raw_shape_root_mode F) tops` by
    simp[deploy_dalloca_form_occurs_def, dynamic_raw_expr_shape,
         dynamic_raw_stmt_shape, EXISTS_MEM] >>
  drule_all (Q.INST [`static` |-> `F`] lower_vyper_deploy_unit_run_mode) >>
  strip_tac >>
  drule_all (Q.INST [`static` |-> `F`] run_deploy_lowering_source_unit_ok_mode) >>
  simp[] >> strip_tac >>
  irule unit_entry_no_params_from_first >> simp[] >>
  drule lower_vyper_deploy_unit_context_ok >>
  simp[lowering_context_ok_def, ctx_fn_names_def]
QED

Theorem lower_vyper_deploy_unit_source_shape_raw_call_calldata:
  !tops rpolicy runtime_bc dunit layouts addr art.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    check_contract T layouts addr [(NONE, tops)] = SOME art /\
    deploy_dalloca_form_occurs
      (\e. ?ty f es d. e = Call ty (RawCallCalldataTarget f) es d) tops ==>
    o1_source_unit_ok dunit /\ unit_entry_no_params dunit
Proof
  metis_tac[lower_vyper_deploy_unit_dynamic_source_unit_shape]
QED

Theorem lower_vyper_deploy_unit_source_shape_create_copy:
  !tops rpolicy runtime_bc dunit layouts addr art.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    check_contract T layouts addr [(NONE, tops)] = SOME art /\
    deploy_dalloca_form_occurs
      (\e. ?ty s r ks es d. e = Call ty (CreateTarget CreateCopyOf s r ks) es d) tops ==>
    o1_source_unit_ok dunit /\ unit_entry_no_params dunit
Proof
  metis_tac[lower_vyper_deploy_unit_dynamic_source_unit_shape]
QED

Theorem lower_vyper_deploy_unit_source_shape_create_blueprint:
  !tops rpolicy runtime_bc dunit layouts addr art.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    check_contract T layouts addr [(NONE, tops)] = SOME art /\
    deploy_dalloca_form_occurs
      (\e. ?ty b s r ks es d.
          e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d) tops ==>
    o1_source_unit_ok dunit /\ unit_entry_no_params dunit
Proof
  metis_tac[lower_vyper_deploy_unit_dynamic_source_unit_shape]
QED

Theorem checked_lower_vyper_deploy_unit_source_shape:
  !tops rpolicy runtime_bc dunit am tx.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    deploy_source_ok tops am tx ==>
    o1_source_unit_ok dunit /\ unit_entry_no_params dunit
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `deploy_dalloca_form_occurs expr_raw_shape_root tops`
  >- (fs[deploy_source_ok_def, deploy_typing_ok_def] >>
      `expr_raw_shape_root =
        (\e. (?ty f es d. e = Call ty (RawCallCalldataTarget f) es d) \/
             ((?ty s r ks es d. e = Call ty (CreateTarget CreateCopyOf s r ks) es d) \/
              (?ty b s r ks es d.
                 e = Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)))` by
        simp[FUN_EQ_THM, expr_raw_shape_root_def, DISJ_ASSOC] >>
      `!R S. deploy_dalloca_form_occurs (\e. R e \/ S e) tops <=>
              deploy_dalloca_form_occurs R tops \/ deploy_dalloca_form_occurs S tops` by
        (simp[deploy_dalloca_form_occurs_def, supported_stmt_expr_exists_disj,
              supported_expr_exists_disj, EXISTS_MEM] >> metis_tac[]) >>
      qpat_x_assum `deploy_dalloca_form_occurs expr_raw_shape_root _` mp_tac >>
      qpat_assum `expr_raw_shape_root = _` (fn th => PURE_REWRITE_TAC [th]) >>
      simp[] >> strip_tac >>
      metis_tac[lower_vyper_deploy_unit_source_shape_raw_call_calldata,
                lower_vyper_deploy_unit_source_shape_create_copy,
                lower_vyper_deploy_unit_source_shape_create_blueprint]) >>
  metis_tac[lower_vyper_deploy_unit_o1_shape_extras_static]
QED

(* ===== The reservation ===== *)

(* Every stage of the O1 pipeline keeps the global reservation: the pass
   runners only replace functions and relabel them. *)
Theorem run_configured_fn_passes_global_reserved[local]:
  run_configured_fn_passes runner rpolicy passes name unit supply =
    SOME (unit',supply') ==>
  unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved
Proof
  simp[run_configured_fn_passes_def] >> strip_tac >> gvs[AllCaseEqs()] >>
  drule apply_unit_label_map_global_reserved >> simp[]
QED

Theorem run_named_fn_schedules_global_reserved[local]:
  !names unit supply unit' supply'.
    run_named_fn_schedules runner rpolicy passes names unit supply =
      SOME (unit',supply') ==>
    unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved
Proof
  Induct >> simp[run_named_fn_schedules_def] >> rpt gen_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule run_configured_fn_passes_global_reserved >>
  first_x_assum drule >> simp[]
QED

Theorem run_pipeline_stages_global_reserved[local]:
  !stages unit supply unit' supply'.
    run_pipeline_stages rpolicy stages unit supply = SOME (unit',supply') ==>
    unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved
Proof
  Induct >> simp[run_pipeline_stages_def] >> Cases >>
  simp[run_pipeline_stage_def, run_mapped_functions_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >>
  imp_res_tac run_named_fn_schedules_global_reserved >> gvs[]
QED

Theorem o1_pipeline_global_reserved:
  !rpolicy unit out.
    o1_pipeline rpolicy unit = SOME out ==>
    out.po_unit.cu_context.ctx_global_reserved =
      unit.cu_context.ctx_global_reserved
Proof
  rpt strip_tac >> fs[o1_pipeline_def] >>
  drule o1_driver_runs >> strip_tac >>
  drule run_pipeline_stages_global_reserved >>
  fs[run_callee_first_def] >>
  drule run_named_fn_schedules_global_reserved >>
  simp[prune_unit_fcg_unreachable_fields]
QED

(* Codegen's context plan exists only for a well-formed reservation. *)
Theorem generate_context_plan_reserved_wf:
  !ctx cp.
    generate_context_plan ctx = SOME cp ==>
    reserved_intervals_wf ctx.ctx_global_reserved
Proof
  rpt strip_tac >> CCONTR_TAC >>
  gvs[generate_context_plan_def, generate_context_plan_with_def,
      max_live_eom_def]
QED

Theorem deploy_unit_o1_shape_ok:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx
    ==>
    o1_source_unit_ok dunit /\
    unit_entry_no_params dunit /\ unit_fmp_unsealed dunit /\
    EVERY (\fn. fn.fn_eom = NONE) dunit.cu_context.ctx_functions /\
    fixed_region_reserved (imm_len tops) dunit.cu_context /\
    reserved_intervals_wf dunit.cu_context.ctx_global_reserved
Proof
  rpt gen_tac >> simp[deploy_phases_def] >>
  strip_tac >>
  drule_all checked_lower_vyper_deploy_unit_source_shape >> strip_tac >>
  drule lower_vyper_deploy_unit_eom_none >> strip_tac >>
  `fixed_region_reserved (imm_len tops) dunit.cu_context` by
    (drule lower_vyper_deploy_unit_global_reserved >>
     rw[fixed_region_reserved_def, imm_len_def] >> gvs[]) >>
  simp[] >>
  drule o1_pipeline_global_reserved >> strip_tac >>
  drule generate_context_plan_reserved_wf >> gvs[]
QED

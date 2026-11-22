(* One execution fuel for a successfully lowered linked runtime. *)
Theory linkedRuntimeFuel
Ancestors
  linkedFuelPackage linkedRawUnitShape compileUnit compileUnitPackageShape
  compileVyper compileEnv vyperCompiler fragFuelUnit fragFuelRuntime fragFuelStmt
  fragFuelStmtBase fragFuelExpr fragFuel ctorDeployRunBounded entryBodyBoundLabels
  loweringShapeProps loweringShapeSource loweringShapeDefs intCallLookup
  supportedExprTraverse venomExecSemantics passSimulationDefs moduleLowering
  list pair rich_list

Triviality package_external_fn_unit_fuel_ok:
  cenv_ptrs_below 0
    (FST (SND (set_external_package_target target
                  (package_external_fn_unit mods trans keys f)))) /\
  (FST (SND (set_external_package_target target
               (package_external_fn_unit mods trans keys f)))).ce_ctor_exit_label = NONE /\
  FST (set_external_package_target target (package_external_fn_unit mods trans keys f)) =
    "fn_" ++ fn_decl_name (SND f)
Proof
  PairCases_on `f` >>
  mp_tac (Q.INST [`src` |-> `f0`, `vis` |-> `External`, `mut` |-> `f1`,
                  `fname` |-> `f4`, `args` |-> `f5`, `ret` |-> `f7`,
                  `ss` |-> `f8`]
    (INST_TYPE [alpha |-> ``:string``] build_compile_env_unit_fuel_ok)) >>
  Cases_on `f7 = NoneT` >>
  simp[package_external_fn_unit_def, set_external_package_target_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def, fn_decl_name_def,
       cenv_ptrs_below_def] >>
  metis_tac[]
QED

Triviality package_fallback_fn_unit_fuel_ok:
  set_fallback_package_target target (package_fallback_fn_unit mods trans keys fb) =
    SOME fb_pkg ==>
  cenv_ptrs_below 0 (FST fb_pkg) /\ (FST fb_pkg).ce_ctor_exit_label = NONE
Proof
  Cases_on `fb`
  >- simp[package_fallback_fn_unit_def, set_fallback_package_target_def] >>
  PairCases_on `x` >>
  mp_tac (Q.INST [`src` |-> `x0`, `vis` |-> `External`, `mut` |-> `x1`,
                  `fname` |-> `x4`, `args` |-> `x5`, `ret` |-> `x7`,
                  `ss` |-> `x8`]
    build_compile_env_unit_fuel_ok) >>
  Cases_on `x7 = NoneT` >>
  simp[package_fallback_fn_unit_def, set_fallback_package_target_def,
       update_cenv_nonreentrant_def, update_cenv_ret_abi_def,
       cenv_ptrs_below_def] >>
  rpt strip_tac >> gvs[] >> res_tac >> metis_tac[]
QED

Triviality package_external_group_unit_fuel_ok:
  (case package_external_group_unit mods target trans keys f of
     ExternalSingle sel pkg =>
       cenv_ptrs_below 0 (FST (SND pkg)) /\
       (FST (SND pkg)).ce_ctor_exit_label = NONE /\
       FST (SND sel) = FST pkg
   | ExternalDefaults common entries specs offset =>
       cenv_ptrs_below 0 common.ec_env /\ common.ec_env.ce_ctor_exit_label = NONE)
Proof
  PairCases_on `f` >>
  mp_tac (Q.INST [`f` |-> `(f0,f1,f2,f3,f4,f5,f6,f7,f8)`]
    package_external_fn_unit_fuel_ok) >>
  simp_tac std_ss [package_external_group_unit_def, LET_THM] >>
  Cases_on `NULL f6`
  >- simp[compute_selector_def, fn_decl_name_def] >>
  simp[] >> pairarg_tac >> gvs[]
QED

Triviality build_selectors_unit_labels_mem:
  EVERY (\sel. MEM (FST (SND sel))
    (MAP FST (MAP (set_external_package_target target o
      package_external_fn_unit mods trans keys) fns)))
    (build_selectors tenv (MAP SND fns))
Proof
  Induct_on `fns` >- simp[build_selectors_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[build_selectors_def, compute_selector_def, package_external_fn_unit_def,
       set_external_package_target_def] >>
  fs[EVERY_MEM]
QED

Theorem lower_vyper_runtime_unit_uniform_fuel_mods:
  lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit ==>
  ?fuel. !n s. terminates (run_context n unit.cu_context s) ==>
               terminates (run_context fuel unit.cu_context s)
Proof
  strip_tac >>
  drule lower_vyper_runtime_unit_raw_shape_mods >> strip_tac >>
  `!fn. MEM fn unit.cu_context.ctx_functions ==>
       ?Kf. !G. callees_stable G unit.cu_context fn ==>
                fuel_stable (G + Kf) unit.cu_context fn` suffices_by
    (strip_tac >> drule_all run_context_uniform_fuel >> metis_tac[]) >>
  qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_mods_def] >>
  pairarg_tac >> simp[bool_case_eq] >> strip_tac >> gvs[]
  >- (qmatch_asmsub_abbrev_tac `run_grouped_lowering groups ips fbp _ _` >>
      `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
        (qpat_assum `Abbrev (ips = _)`
          (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         drule (Q.INST [`static` |-> `F`] package_internal_fn_unit_shape) >>
         impl_tac >- simp[EVERY_MEM, FORALL_PROD, expr_shape_root_mode_dynamic,
                          dynamic_raw_expr_shape, dynamic_raw_stmt_shape] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `run_grouped_lowering _ _ _ _ _ = _` mp_tac >>
      simp[run_grouped_lowering_def] >> pairarg_tac >>
      simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
      `ALL_DISTINCT (MAP FST (internal_fn_descriptors ips))` by
        (drule_all_then ACCEPT_TAC extract_context_descriptors_distinct) >>
      qpat_x_assum `compile_generate_grouped_runtime _ _ _ _ = _`
        (assume_tac o REWRITE_RULE [compile_generate_grouped_runtime_split]) >>
      qmatch_asmsub_abbrev_tac
        `comp_ignore_bind prefix (comp_bind (compile_internal_fn_bodies ips) _) _` >>
      match_mp_tac (Q.SPECL [`prefix`, `ips`, `st1`, `ctx`, `data`]
        split_unit_fns_stable) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
        >- (qpat_x_assum `Abbrev (prefix = _)` (SUBST1_TAC o
              REWRITE_RULE [markerTheory.Abbrev_def]) >>
            qsuff_tac `EVERY (\l. l = "__entry" \/ jump_label_ok l)
              (MAP (\bb. bb.bb_label) (all_blocks
                (SND (compile_generate_grouped_runtime groups [] fbp
                  (initial_compile_state "__entry")))))`
            >- simp[compile_generate_grouped_runtime_split,
                    compile_internal_fn_bodies_def, comp_ignore_bind_def,
                    comp_bind_def, comp_return_def, ELIM_UNCURRY] >>
            irule bound_labels_runtime_grouped_no_internals >>
            simp[jump_label_ok_def, initial_compile_state_def, all_blocks_def,
                 Abbr `groups`, EVERY_MAP, EVERY_MEM] >>
            rpt strip_tac >> PairCases_on `x` >>
            simp[package_external_group_unit_def, package_external_fn_unit_def,
                 set_external_package_target_def, external_group_labels_ok_def,
                 external_common_label_def, external_prefix_label_def,
                 compute_selector_def, EVERY_MAP, FORALL_PROD, IS_PREFIX_APPEND] >>
            IF_CASES_TAC >> simp[external_group_labels_ok_def, compute_selector_def,
              EVERY_MAP, EVERY_MEM, FORALL_PROD])
        >- (qunabbrev_tac `prefix` >>
            match_mp_tac (SIMP_RULE (srw_ss ())
              [fuel_ok_compile_expr, fuel_okS_compile_stmt] fuel_okS_grouped_runtime_entry_prefix) >>
            rpt conj_tac
            >- (simp[Abbr `groups`, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
                mp_tac (Q.INST [`f` |-> `x`, `target` |-> `rpolicy.rpol_target`,
                               `trans` |-> `T`, `keys` |-> `K global_nonreentrant_slot`]
                  package_external_group_unit_fuel_ok) >>
                Cases_on `package_external_group_unit mods rpolicy.rpol_target T
                  (K global_nonreentrant_slot) x` >> simp[])
            >- (simp[Abbr `groups`, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
                mp_tac (Q.INST [`f` |-> `x`, `target` |-> `rpolicy.rpol_target`,
                               `trans` |-> `T`, `keys` |-> `K global_nonreentrant_slot`]
                  package_external_group_unit_fuel_ok) >>
                Cases_on `package_external_group_unit mods rpolicy.rpol_target T
                  (K global_nonreentrant_slot) x` >> simp[]) >>
            rw[Abbr `fbp`] >> drule package_fallback_fn_unit_fuel_ok >> simp[]) >>
      simp[Abbr `ips`, package_internal_fns_unit_fuel]) >>
  qmatch_asmsub_abbrev_tac `run_lowering sels eps ips fbp _ _ _ _ _ _` >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    (qpat_assum `Abbrev (ips = _)`
      (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule (Q.INST [`static` |-> `F`] package_internal_fn_unit_shape) >>
     impl_tac >- simp[EVERY_MEM, FORALL_PROD, expr_shape_root_mode_dynamic,
                      dynamic_raw_expr_shape, dynamic_raw_stmt_shape] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  drule run_lowering_descriptors_distinct >> strip_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def] >> pairarg_tac >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  qpat_assum `rpolicy.rpol_frontend_dispatch = Linear` (fn th =>
    qpat_x_assum `compile_generate_runtime _ _ _ _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th, compile_generate_runtime_linear_split])) >>
  qmatch_asmsub_abbrev_tac
    `comp_ignore_bind prefix (comp_bind (compile_internal_fn_bodies ips) _) _` >>
  match_mp_tac (Q.SPECL [`prefix`, `ips`, `st1`, `ctx`, `data`]
    split_unit_fns_stable) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (qunabbrev_tac `prefix` >>
        qsuff_tac `EVERY (\l. l = "__entry" \/ jump_label_ok l)
          (MAP (\bb. bb.bb_label) (all_blocks
            (SND (compile_generate_runtime sels eps [] fbp Linear 0 0 []
              (build_dense_entry_info sels eps) (initial_compile_state "__entry")))))`
        >- simp[compile_generate_runtime_linear_split, compile_internal_fn_bodies_def,
                comp_ignore_bind_def, comp_bind_def, comp_return_def, ELIM_UNCURRY] >>
        irule bound_labels_runtime_linear_no_internals >>
        simp[jump_label_ok_def, initial_compile_state_def, all_blocks_def,
             Abbr `eps`, EVERY_MAP, EVERY_MEM] >>
        rpt strip_tac >> PairCases_on `x` >>
        simp[package_external_fn_unit_def, set_external_package_target_def,
             jump_label_ok_def, IS_PREFIX_APPEND])
    >- (qunabbrev_tac `prefix` >>
        match_mp_tac (SIMP_RULE (srw_ss ()) [fuel_okS_compile_stmt]
          fuel_okS_runtime_entry_prefix) >>
        rpt conj_tac
        >- simp[Abbr `eps`, EVERY_MAP, package_external_fn_unit_fuel_ok]
        >- simp[Abbr `sels`, Abbr `eps`, build_selectors_unit_labels_mem] >>
        rw[Abbr `fbp`] >> drule package_fallback_fn_unit_fuel_ok >> simp[]) >>
  simp[Abbr `ips`, package_internal_fns_unit_fuel]
QED

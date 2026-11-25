Theory linkedLinearShadowBodyInv
Ancestors
  linkedCompiledCalleeSource linkedShadowBodyInvRuns bodyFullShadowInternalRun
  bodyFullShadowBodyInv gasShadowUnitExtract compileVyper loweringShapeProps compileUnit moduleLowering
  compileEnv vyperCompiler gasShadowRunLowering gasShadowRuntime gasShadowState
  gasShadowUnit gasShadowModuleDefs gasShadow constSubstMods venomInst list pair option

Theorem linear_runtime_shadow_body_inv_mods:
  check_contract F layouts addr mods = SOME art /\
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  ~EXISTS (external_has_defaults o SND) exts /\
  sels = build_selectors (type_env_all_modules mods) (MAP SND exts) /\
  packs = MAP (set_external_package_target rp.rpol_target o
    package_external_fn_unit mods T (K global_nonreentrant_slot)) exts /\
  ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) F 0)
      (order_internals_unit
        (runtime_internal_order_unit (exported_runtime_fns mods exps)
          (main_module mods) ints) ints) /\
  fall = set_fallback_package_target rp.rpol_target
    (package_fallback_fn_unit mods T (K global_nonreentrant_slot) fb) /\
  info = build_dense_entry_info sels packs /\
  run_lowering sels (MAP gas_shadow_external_package packs)
    (MAP gas_shadow_internal_package ips) (OPTION_MAP gas_shadow_fallback_package fall)
    rp 0 0 [] info "__entry" = SOME shadow_unit ==>
  shadow_body_inv_mods mods exps unit.cu_context shadow_unit.cu_context
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `srcs = order_internals_unit
    (runtime_internal_order_unit (exported_runtime_fns mods exps)
      (main_module mods) ints) ints` >>
  `ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) F 0) srcs` by
    simp[Abbr `srcs`] >>
  `run_lowering sels packs ips fall rp 0 0 [] info "__entry" = SOME unit` by
    (qpat_assum `classify_functions_unit _ _ = _` (fn classified =>
       qpat_assum `lower_vyper_runtime_unit_mods _ _ _ = _`
         (mp_tac o PURE_REWRITE_RULE [lower_vyper_runtime_unit_mods_def, LET_THM, classified])) >>
     CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
     qpat_assum `~EXISTS (external_has_defaults o SND) exts`
       (fn no_defaults => rewrite_tac[no_defaults]) >>
     IF_CASES_TAC >> simp[]) >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels` by
    (qpat_assum `sels = build_selectors _ _` SUBST1_TAC >>
     MATCH_ACCEPT_TAC build_selectors_fn_labels) >>
  `EVERY (\pkg. isPREFIX "fn_" (FST pkg)) packs` by
    (qpat_assum `packs = MAP _ exts` SUBST1_TAC >>
     simp[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
          package_external_fn_unit_def, set_external_package_target_def, LET_THM]) >>
  `EVERY (\pkg. isPREFIX "fn_" (FST pkg)) (MAP gas_shadow_external_package packs)` by
    (qpat_assum `EVERY (\pkg. isPREFIX "fn_" (FST pkg)) packs`
      (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     simp_tac bool_ss [EVERY_MAP, EVERY_MEM] >>
     disch_tac >> qx_gen_tac `pkg` >> strip_tac >>
     first_x_assum (qspec_then `pkg` mp_tac) >>
     PairCases_on `pkg` >> simp[gas_shadow_external_package_def]) >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    (qpat_assum `ips = MAP _ srcs` SUBST1_TAC >>
     simp[unit_package_internal_labels]) >>
  `EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors (MAP gas_shadow_internal_package ips))` by
    (PURE_REWRITE_TAC [gas_shadow_internal_fn_descriptors] >>
     FIRST_ASSUM ACCEPT_TAC) >>
  qpat_assum `run_lowering sels packs ips fall _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_internal_run_labels) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`start`,`final`,`data`] strip_assume_tac) >>
  qpat_assum `run_lowering sels (MAP gas_shadow_external_package packs) _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_internal_run_labels) >>
  impl_tac >- asm_rewrite_tac[] >>
  disch_then (qx_choosel_then [`startS`,`finalS`,`dataS`] strip_assume_tac) >>
  `gas_shadow_state start startS` by
    (qspecl_then [`sels`,`packs`,`[]`,`fall`,`Linear`,`0`,`0`,`[]`,`info`]
       mp_tac gas_shadow_compile_generate_runtime >>
     rewrite_tac[gas_shadow_compiles_def, MAP] >>
     disch_then (qspecl_then [`initial_compile_state "__entry"`,
       `initial_compile_state "__entry"`] mp_tac) >>
     asm_rewrite_tac[gas_shadow_state_refl]) >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    (qspecl_then [`sels`,`packs`,`ips`,`fall`,`rp`,`0`,`0`,`[]`,`info`,`"__entry"`]
       mp_tac gas_shadow_run_lowering >>
     asm_rewrite_tac[] >> simp[optionTheory.OPTREL_def, gas_shadow_unit_def]) >>
  mp_tac (Q.INST [`is_ctor` |-> `F`, `name` |-> `"__entry"`,
    `bc` |-> `[]`, `unit` |-> `unit`, `shadow_unit` |-> `shadow_unit`,
    `raw` |-> `unit.cu_context`, `rawS` |-> `shadow_unit.cu_context`,
    `srcs` |-> `srcs`, `ips` |-> `ips`, `start` |-> `start`, `startS` |-> `startS`,
    `run_end` |-> `final`, `run_endS` |-> `finalS`, `data` |-> `data`, `dataS` |-> `dataS`]
    (SPEC_ALL shadow_body_inv_mods_from_internal_runs)) >>
  impl_tac
  >- (asm_rewrite_tac[] >> simp_tac bool_ss [] >>
     qx_genl_tac [`src`,`tops`,`mode`,`vis`,`mut`,`nr`,`rr`,`fname`,`args`,`dflts`,`ret`,`ss`,`callee`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     mp_tac (Q.INST [`is_ctor` |-> `F`, `rp` |-> `rp`, `exps` |-> `exps`,
        `ctx` |-> `unit.cu_context`, `raw` |-> `unit.cu_context`,
        `name` |-> `"__entry"`, `ips` |-> `ips`, `final` |-> `final`, `data` |-> `data`,
        `srcs` |-> `srcs`, `imp_ctors` |-> `imp_ctors`]
        (SPEC_ALL linked_compiled_callee_source_member)) >>
     simp_tac bool_ss [COND_CLAUSES] >>
     asm_rewrite_tac[] >>
     impl_tac >-
       (qx_gen_tac `pkg` >> PairCases_on `pkg` >>
        qpat_assum `Abbrev (srcs = _)` (fn eq =>
          PURE_REWRITE_TAC [REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
        disch_then (assume_tac o MATCH_MP order_internals_unit_mem) >>
        simp[]) >>
     simp[]) >>
  disch_then ACCEPT_TAC
QED

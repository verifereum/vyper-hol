Theory linkedGroupedShadowBodyInv
Ancestors
  linkedShadowBodyInvRuns bodyFullShadowInternalRun bodyFullShadowInternalCode
  bodyFullShadowBodyInv groupedInternalLabels gasShadowRunLowering gasShadowRuntime
  gasShadowModuleDefs gasShadowUnit gasShadowState gasShadow
  compileUnit compileVyper compileEnv moduleLowering constSubstMods
  loweringShapeDefs vyperCompiler venomInst list pair option rich_list alist

Theorem grouped_runtime_shadow_body_inv_mods:
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,ctor,imp_ctors) /\
  EXISTS (external_has_defaults o SND) exts /\
  groups = MAP (package_external_group_unit mods rp.rpol_target T
    (K global_nonreentrant_slot)) exts /\
  ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) F 0)
      (order_internals_unit
        (runtime_internal_order_unit (exported_runtime_fns mods exps)
          (main_module mods) ints) ints) /\
  fall = set_fallback_package_target rp.rpol_target
    (package_fallback_fn_unit mods T (K global_nonreentrant_slot) fb) /\
  shadow_groups = MAP (\group. case group of
      ExternalSingle selector package =>
        ExternalSingle selector (gas_shadow_external_package package)
    | ExternalDefaults common entries specs head_offset =>
        ExternalDefaults
          (common with <|ec_env := gas_shadow_env T common.ec_env;
                         ec_body := MAP gas_shadow_stmt common.ec_body|>)
          entries
          (MAP (\(name,ty,e). (name,ty,gas_shadow_expr e)) specs)
          head_offset) groups ==>
  ?shadow_unit.
    run_grouped_lowering shadow_groups (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fall) rp "__entry" = SOME shadow_unit /\
    gas_shadow_unit unit shadow_unit /\
    shadow_body_inv_mods mods exps unit.cu_context shadow_unit.cu_context
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `srcs = order_internals_unit
    (runtime_internal_order_unit (exported_runtime_fns mods exps)
      (main_module mods) ints) ints` >>
  `ips = MAP (set_internal_package_target rp.rpol_target o
      package_internal_fn_unit mods T (K global_nonreentrant_slot) F 0) srcs` by
    simp[Abbr `srcs`] >>
  `run_grouped_lowering groups ips fall rp "__entry" = SOME unit` by
    (qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
     simp[lower_vyper_runtime_unit_mods_def, AllCaseEqs(), Abbr `srcs`]) >>
  `?shadow_unit.
     run_grouped_lowering shadow_groups (MAP gas_shadow_internal_package ips)
       (OPTION_MAP gas_shadow_fallback_package fall) rp "__entry" = SOME shadow_unit /\
     gas_shadow_unit unit shadow_unit` by
    (qspecl_then [`groups`,`ips`,`fall`,`rp`,`"__entry"`]
       mp_tac gas_shadow_run_grouped_lowering >>
     qpat_assum `shadow_groups = MAP _ groups` (PURE_REWRITE_TAC o single o GSYM) >>
     asm_rewrite_tac[] >> simp[optionTheory.OPTREL_def, AllCaseEqs()]) >>
  qexists_tac `shadow_unit` >> asm_rewrite_tac[] >>
  `EVERY group_entry_labels_ok groups` by
    (qpat_assum `groups = MAP _ exts` SUBST1_TAC >>
     simp[EVERY_MAP, package_external_group_unit_labels]) >>
  `!group. group_entry_labels_ok (case group of
           ExternalSingle selector package =>
             ExternalSingle selector (gas_shadow_external_package package)
         | ExternalDefaults common entries specs head_offset =>
             ExternalDefaults
               (common with <|ec_env := gas_shadow_env T common.ec_env;
                              ec_body := MAP gas_shadow_stmt common.ec_body|>)
               entries (MAP (\(name,ty,e). (name,ty,gas_shadow_expr e)) specs)
               head_offset) <=> group_entry_labels_ok group` by
    (Cases >> simp[group_entry_labels_ok_def] >>
     rename1 `(internal_label_ok (FST (gas_shadow_external_package package)) <=> _)` >>
     PairCases_on `package` >> simp[gas_shadow_external_package_def]) >>
  `EVERY group_entry_labels_ok shadow_groups` by
    (qpat_assum `shadow_groups = MAP _ groups` SUBST1_TAC >>
     simp_tac bool_ss [EVERY_MAP, EVERY_MEM, combinTheory.o_DEF] >>
     qx_gen_tac `group` >> strip_tac >>
     qpat_assum `!g. group_entry_labels_ok _ <=> group_entry_labels_ok g`
       (qspec_then `group` (fn label_eq => PURE_REWRITE_TAC [label_eq])) >>
     qpat_assum `EVERY group_entry_labels_ok groups`
       (drule_then ACCEPT_TAC o REWRITE_RULE [EVERY_MEM])) >>
  qpat_assum `run_grouped_lowering groups ips fall _ _ = _`
    (mp_then Any mp_tac grouped_internal_run_labels) >>
  impl_tac >- FIRST_ASSUM ACCEPT_TAC >>
  disch_then (qx_choosel_then [`start`,`run_end`,`data`] strip_assume_tac) >>
  qpat_assum `run_grouped_lowering shadow_groups _ _ _ _ = _`
    (mp_then Any mp_tac grouped_internal_run_labels) >>
  impl_tac >- FIRST_ASSUM ACCEPT_TAC >>
  disch_then (qx_choosel_then [`startS`,`run_endS`,`dataS`] strip_assume_tac) >>
  `gas_shadow_state start startS` by
    (qspecl_then [`groups`,`[]`,`fall`] mp_tac
       (Q.INST [`sd` |-> `T`] gas_shadow_compile_generate_grouped_runtime) >>
     qpat_assum `shadow_groups = MAP _ groups` (PURE_REWRITE_TAC o single o GSYM) >>
     rewrite_tac[gas_shadow_compiles_def, listTheory.MAP] >>
     disch_then (qspecl_then [`initial_compile_state "__entry"`,
                              `initial_compile_state "__entry"`] mp_tac) >>
     simp[gas_shadow_state_refl]) >>
  `!src tops mode vis mut nr rr fname args dflts ret ss callee.
      ALOOKUP mods src = SOME tops /\
      (vis = Internal \/ (mode /\ src <> NONE /\ vis = Deploy)) /\
      MEM (FunctionDecl vis mut nr rr fname args dflts ret ss) tops /\
      lookup_function
        (internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,fname)))
          (nsid_to_string (src,fname)) (MAP SND args) mode)
        unit.cu_context.ctx_functions = SOME callee ==>
      mode = F /\ MEM (src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,rr,fname,args,dflts,ret,ss)) srcs` by
    (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     `mode = F` by
       (qpat_assum `lookup_function _ _ = _`
          (mp_tac o MATCH_MP lookup_function_mem) >>
        qpat_assum `extract_context_with_internals "__entry" ips run_end = _`
          (PURE_REWRITE_TAC o single o MATCH_MP extract_context_internal_names) >>
        qpat_assum `ips = MAP _ srcs` SUBST1_TAC >>
        simp[internal_fn_descriptors_map, GSYM MAP_MAP_o, MEM_MAP] >>
        strip_tac
        >- fs[internal_fn_label_def] >>
        rename1 `MEM packed srcs` >> PairCases_on `packed` >>
        fs[package_internal_fn_unit_def, set_internal_package_target_def] >>
        metis_tac[internal_fn_label_mode]) >>
     qpat_x_assum `mode = F` SUBST_ALL_TAC >>
     qpat_x_assum `vis = Internal \/ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
     `MEM (src,subst_consts_fn_mods (consts_env_mods mods)
         (mut,nr,rr,fname,args,dflts,ret,ss))
         (FST (SND (classify_functions_unit mods exps)))` by
       (irule classified_unit_internal_member >> qexists_tac `tops` >> fs[]) >>
     qpat_assum `classify_functions_unit mods exps = _` (fn classes =>
       qpat_assum `MEM _ (FST (SND (classify_functions_unit mods exps)))`
         (mp_tac o REWRITE_RULE [classes])) >>
     simp[Abbr `srcs`, order_internals_unit_mem]) >>
  mp_tac (Q.INST [`is_ctor` |-> `F`, `name` |-> `"__entry"`,
      `unit` |-> `unit`, `shadow_unit` |-> `shadow_unit`,
      `raw` |-> `unit.cu_context`, `rawS` |-> `shadow_unit.cu_context`,
      `srcs` |-> `srcs`, `ips` |-> `ips`,
      `start` |-> `start`, `startS` |-> `startS`,
      `run_end` |-> `run_end`, `run_endS` |-> `run_endS`,
      `data` |-> `data`, `dataS` |-> `dataS`]
    (SPEC_ALL shadow_body_inv_mods_from_internal_runs)) >>
  impl_tac >-
    (simp_tac bool_ss [] >> asm_rewrite_tac[] >>
     conj_tac >-
       (qpat_assum `!src tops mode vis mut nr rr fname args dflts ret ss callee. _` mp_tac >>
        simp_tac bool_ss [CONJ_ASSOC]) >>
     qpat_assum `gas_shadow_unit unit shadow_unit`
       (ACCEPT_TAC o cj 2 o REWRITE_RULE [gas_shadow_unit_def])) >>
  disch_then ACCEPT_TAC
QED

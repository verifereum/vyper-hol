Theory linkedGroupedShadowBodyInv
Ancestors
  linkedShadowBodyInvRuns bodyFullShadowInternalRun bodyFullShadowInternalCode
  bodyFullShadowBodyInv groupedInternalLabels gasShadowRunLowering gasShadowRuntime
  gasShadowModuleDefs gasShadowUnit gasShadowState gasShadow
  compileUnit compileVyper compileEnv moduleLowering constSubstMods
  loweringShapeDefs vyperCompiler venomInst list pair option rich_list alist
  linkedInternalSelection linkedCheckedDeclarationNames whitelistCheckerSelectorProps
  vyperTypeContractContext vyperTypeContract

Theorem grouped_runtime_shadow_body_inv_mods:
  check_contract F layouts addr mods = SOME art /\
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
  `ALL_DISTINCT (MAP FST mods)` by
    (drule check_contract_namespaces_ok >> simp[contract_namespaces_ok_def]) >>
  `!src tops. ALOOKUP mods src = SOME tops ==> supported_declaration_names tops` by
    (rpt strip_tac >>
     `MEM (src,tops) mods` by drule_then ACCEPT_TAC ALOOKUP_MEM >>
     `supported_selectors_distinct tops` by
       drule_all_then ACCEPT_TAC check_contract_module_selectors_distinct >>
     drule_all check_contract_supported_declaration_names_mods >> simp[]) >>
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
     `?selected. MEM selected srcs /\
       internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,fname)))
         (nsid_to_string (src,fname)) (MAP SND args) mode =
       FST (set_internal_package_target rp.rpol_target
         (package_internal_fn_unit mods T (K global_nonreentrant_slot) F 0 selected))` by
       (qpat_assum `lookup_function _ _ = _`
          (mp_tac o MATCH_MP lookup_function_mem) >>
        qpat_assum `extract_context_with_internals "__entry" ips run_end = _`
          (PURE_REWRITE_TAC o single o MATCH_MP extract_context_internal_names) >>
        qpat_assum `ips = MAP _ srcs` SUBST1_TAC >>
        simp[internal_fn_descriptors_map, GSYM MAP_MAP_o, MEM_MAP] >>
        strip_tac
        >- fs[internal_fn_label_def] >>
        rename1 `MEM packed srcs` >> qexists_tac `packed` >>
        PairCases_on `packed` >>
        fs[package_internal_fn_unit_def, set_internal_package_target_def]) >>
     PairCases_on `selected` >>
     qpat_x_assum `internal_fn_label _ _ _ _ = FST _` mp_tac >>
     simp[package_internal_fn_unit_def, set_internal_package_target_def] >>
     strip_tac >>
     `mode = F` by metis_tac[internal_fn_label_mode] >>
     `MEM (selected0,selected1,selected2,selected3,selected4,selected5,
             selected6,selected7,selected8) (ints ++ imp_ctors)` by
       (simp[MEM_APPEND] >> disj1_tac >>
        irule order_internals_unit_mem >>
        qexists_tac `runtime_internal_order_unit (exported_runtime_fns mods exps)
          (main_module mods) ints` >>
        qpat_assum `Abbrev (srcs = _)`
          (fn source_eq => PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] source_eq)]) >>
        first_assum ACCEPT_TAC) >>
     qpat_x_assum `internal_fn_label _ _ _ _ = _`
       (assume_tac o GSYM o MATCH_MP internal_fn_label_id_11) >>
     `(selected0,selected1,selected2,selected3,selected4,selected5,
       selected6,selected7,selected8) =
       (src,subst_consts_fn_mods (consts_env_mods mods)
          (mut,nr,rr,fname,args,dflts,ret,ss))` by
       (mp_tac (Q.INST [`exps` |-> `exps`,`exts` |-> `exts`,`ints` |-> `ints`,
          `fb` |-> `fb`,`ctor` |-> `ctor`,`imp_ctors` |-> `imp_ctors`,
          `tops` |-> `tops`,`vis` |-> `vis`,
          `src'` |-> `selected0`,
          `picked` |-> `(selected1,selected2,selected3,selected4,selected5,
                           selected6,selected7,selected8)`,
          `stmts` |-> `ss`] checked_classified_internal_id_unique) >>
        `vis = Internal` by fs[] >>
        simp[fn_decl_name_def] >>
        disch_then (fn unique =>
          qpat_assum `!s ts. ALOOKUP mods s = SOME ts ==> supported_declaration_names ts`
            (ACCEPT_TAC o MATCH_MP unique))) >>
     asm_rewrite_tac[] >> metis_tac[]) >>
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

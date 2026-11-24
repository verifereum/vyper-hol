Theory bodyFullShadowBodyInvLowering
Ancestors
  bodyFullShadowBodyInv bodyFullShadowInternalCode bodyFullShadowInternalRun gasShadowRunLowering
  gasShadowDeployRunner gasShadowModuleDefs gasShadow gasShadowUnit
  gasShadowState gasShadowShape gasShadowRuntime gasShadowDeploy
  gasShadowUnitExtract gasShadowInternal
  compileVyper vyperCompiler compileEnv moduleLowering immSectionDead
  loweringShapeProps loweringShapeDefs loweringShapeSource
  ctorDeployLoweringCode ctorDeployLoweringDefs ctorDeployDefs ctorGeneratorShape
  supportedProgram supportedDecls constSubst venomInst venomWf list rich_list
  venomCompilerTypes sorting constSubstStmtsPreserve supportedNameRoot
  vyperTypeContractStaticMaps e2eDeployDefs bodySim ctorDeployShape
  bodyInvSplit bodySimModsProps
  bodyCallSupport entryCreateInternalSource
  compileUnit constSubstMods groupedInternalLabels alist pair loweringShapeRules
  context emitHelper stmtLowering
  vyperGetter publicGetterProps supportedNames supportedStmts supportedStmtTraverse
  supportedExprs vyperContext vyperTypeContract vyperTypeCallGraph typedCopyDomain
Libs
  monadsyntax

Theorem shadow_body_inv_from_internal_runs[local]:
  (if is_ctor then lower_vyper_deploy_unit tops rp bc = SOME unit
   else lower_vyper_runtime_unit tops rp = SOME unit) /\
  name = (if is_ctor then "__deploy" else "__entry") /\
  srcs = order_internals keys (FST (SND (classify_functions tops))) /\
  (enriched ==> supported_program tops) /\
  (~enriched ==> PERM srcs (FST (SND (classify_functions tops)))) /\
  ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn tops T (K global_nonreentrant_slot) is_ctor
      (if is_ctor then imm_len tops else 0)) srcs /\
  compile_internal_fn_bodies ips start = ((),run_end) /\
  compile_internal_fn_bodies (MAP gas_shadow_internal_package ips)
    startS = ((),run_endS) /\
  extract_context_with_internals name ips run_end = SOME (raw,data) /\
  extract_context_with_internals name (MAP gas_shadow_internal_package ips)
    run_endS = SOME (rawS,dataS) /\
  unit.cu_context.ctx_functions = raw.ctx_functions /\
  shadow_unit.cu_context.ctx_functions = rawS.ctx_functions /\
  gas_shadow_context unit.cu_context shadow_unit.cu_context /\
  lowering_context_ok unit.cu_context /\ lowering_context_ok shadow_unit.cu_context /\
  gas_shadow_state start startS /\
  EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start) /\
  EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks startS) ==>
  shadow_body_inv_with
    (\a b. enriched ==> ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b)))
    tops unit.cu_context shadow_unit.cu_context
Proof
  strip_tac >>
  simp[shadow_body_inv_with_def, shadow_body_inv_mods_with_def,
       ALOOKUP_def, optionTheory.FORALL_OPTION, nsid_to_string_def,
       build_func_ids_mods_singleton, lower_vyper_runtime_unit_mods_singleton,
       lower_vyper_deploy_unit_mods_singleton, package_internal_fn_unit_singleton,
       imm_len_mods_singleton, immSectionDeadTheory.imm_len_def,
       consts_env_mods_singleton, subst_consts_fn_mods_singleton,
       subst_consts_mods_singleton] >> rpt gen_tac >> strip_tac >>
  rename1 `lookup_function (internal_fn_label _ fname _ mode) _ = SOME callee` >>
  `mode = is_ctor` by
    (mp_tac (Q.INST [`target` |-> `rp.rpol_target`,
      `cap` |-> `if is_ctor then imm_len tops else 0`, `id` |-> `build_func_ids 0 tops fname`,
      `tys` |-> `MAP SND (args : (string # type) list)`] packaged_internal_mode) >> fs[]) >>
  qpat_x_assum `mode = is_ctor` SUBST_ALL_TAC >>
  qabbrev_tac `src = subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,fname,args,dflts,ret,ss)` >>
  `MEM src srcs` by
    (Cases_on `enriched`
     >- (qpat_assum `extract_context_with_internals name ips run_end = SOME (raw,data)`
           (assume_tac o MATCH_MP extract_context_internal_names) >>
         `MAP (\f. f.fn_name) raw.ctx_functions = name :: MAP FST
           (internal_fn_descriptors (MAP (set_internal_package_target rp.rpol_target o
             package_internal_fn tops T (K global_nonreentrant_slot) is_ctor
               (if is_ctor then imm_len tops else 0)) srcs))` by simp[] >>
         `lookup_function (internal_fn_label (build_func_ids 0 tops fname) fname
           (MAP SND args) is_ctor) raw.ctx_functions = SOME callee` by metis_tac[] >>
         `internal_fn_label (build_func_ids 0 tops fname) fname (MAP SND args) is_ctor <>
           name` by (Cases_on `is_ctor` >> fs[internal_fn_label_def]) >>
         `supported_program tops` by fs[] >>
         simp_tac bool_ss [Abbr `src`] >>
         drule_all selected_ordered_internal_source >> disch_then ACCEPT_TAC) >>
     `PERM srcs (FST (SND (classify_functions tops)))` by fs[] >>
     qpat_assum `PERM srcs _` (mp_tac o MATCH_MP PERM_MEM_EQ) >>
     disch_then (qspec_then `src` SUBST1_TAC) >>
     simp[Abbr `src`, subst_consts_fn_def, MEM_classify_internal] >>
     qexistsl [`dflts`, `ss`] >> simp[]) >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    simp[package_internal_labels] >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors ips))` by
    (qpat_assum `extract_context_with_internals name ips run_end = SOME (raw,data)`
       (strip_assume_tac o MATCH_MP extract_context_internal_names) >>
     qpat_assum `lowering_context_ok unit.cu_context`
       (mp_tac o REWRITE_RULE [lowering_context_ok_def, ctx_fn_names_def]) >>
     asm_rewrite_tac[] >> simp[]) >>
  `gas_shadow_state run_end run_endS` by
    (mp_tac (Q.SPEC `ips` gas_shadow_compile_internal_fn_bodies) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`start`, `startS`] mp_tac) >> gvs[]) >>
  `gas_shadow_context raw rawS` by
    (mp_tac (Q.ISPECL [`run_end : compile_state`, `run_endS : compile_state`, `name : string`,
       `ips : (string # compile_env # (string # bool) list #
         bool # bool # num # bool # bool # bool # num # stmt list # type option) list`]
       gas_shadow_extract_context_with_internals) >>
     gvs[optionTheory.OPTREL_def]) >>
  qabbrev_tac `pkg = set_internal_package_target rp.rpol_target
    (package_internal_fn tops T (K global_nonreentrant_slot) is_ctor
      (if is_ctor then imm_len tops else 0) src)` >>
  `MEM pkg ips` by
    (qpat_assum `ips = MAP _ srcs` (fn th => simp_tac bool_ss [th, MEM_MAP]) >>
     qexists_tac `src` >> simp_tac bool_ss [Abbr `pkg`, combinTheory.o_THM] >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `ips = MAP _ srcs` kall_tac >>
  qpat_x_assum `MEM pkg ips` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  rename1 `ips = xs ++ pkg::ys` >>
  PairCases_on `pkg` >>
  rename1 `Abbrev ((label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt) = _)` >>
  `set_internal_package_target rp.rpol_target
    (package_internal_fn tops T (K global_nonreentrant_slot) is_ctor
      (if is_ctor then imm_len tops else 0) src) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt)` by
    (qpat_assum `Abbrev ((label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,
        compiled_ss,rt) = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >> simp[]) >>
  `label = internal_fn_label (build_func_ids 0 tops fname) fname
     (MAP SND args) is_ctor /\
   compiled_ss = subst_consts_stmts (module_consts_env tops []) ss` by
    (qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [Abbr `src`, subst_consts_fn_def, package_internal_fn_def,
       LET_THM, set_internal_package_target_def]) >>
  mp_tac (Q.INST [`pkg` |-> `(label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt)`,
    `nr` |-> `nr'`, `ss` |-> `compiled_ss`, `ctx` |-> `raw`, `sctx` |-> `rawS`,
    `sdata` |-> `dataS`, `sips` |-> `MAP gas_shadow_internal_package ips`]
    (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] selected_internal_shadow_layout)) >>
  impl_tac >-
    (fs[lowering_context_ok_def, ctx_fn_names_def, fn_labels_def,
        ctx_inst_ids_distinct_def, EVERY_MEM] >>
     metis_tac[]) >>
  strip_tac >>
  qexistsl_tac [`rp`, `unit`, `label`, `ce`, `params`, `has_rb`, `nr'`, `key`,
    `trans`, `view`, `ctor`, `ilen`, `rt`] >>
  gs[Abbr `src`, imm_len_def, bool_case_eq, lowering_context_ok_def] >>
  metis_tac[]
QED

Theorem runtime_grouped_shadow_body_with_fixed[local]:
  (enriched ==> supported_program tops) /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  lower_vyper_runtime_unit tops rp = SOME unit /\
  runtime_gas_shadow_unit tops rp = SOME shadow_unit ==>
  shadow_body_inv_with
    (\a b. enriched ==> ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b)))
    tops unit.cu_context shadow_unit.cu_context
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = packages` >> PairCases_on `packages` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor_src)` >>
  `EXISTS external_has_defaults exts` by fs[] >>
  `gas_shadow_unit unit shadow_unit` by
    (drule_all runtime_gas_shadow_unit_exists >> simp[]) >>
  qpat_assum `lower_vyper_runtime_unit _ _ = _`
    (mp_tac o REWRITE_RULE [lower_vyper_runtime_unit_def]) >>
  simp[AllCaseEqs()] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_grouped_lowering groups ips fall rp "__entry"` >>
  `EVERY group_entry_labels_ok groups` by
    simp[Abbr `groups`, EVERY_MAP, package_external_group_labels] >>
  qpat_x_assum `runtime_gas_shadow_unit _ _ = _` mp_tac >>
  simp[runtime_gas_shadow_unit_def, Abbr `groups`, Abbr `ips`, Abbr `fall`] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac
    `run_grouped_lowering shadow_groups (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fall) rp "__entry"` >>
  `EVERY group_entry_labels_ok shadow_groups` by
    (fs[Abbr `shadow_groups`, EVERY_MAP, EVERY_MEM] >>
     rpt strip_tac >> rename1 `MEM external exts` >>
     `group_entry_labels_ok
       (package_external_group tops rp.rpol_target T (K global_nonreentrant_slot) external)` by
       simp[package_external_group_labels] >>
     Cases_on `package_external_group tops rp.rpol_target T (K global_nonreentrant_slot) external` >>
     gvs[group_entry_labels_ok_def] >>
     rename1 `~internal_label_ok (FST (gas_shadow_external_package pkg))` >>
     PairCases_on `pkg` >> fs[gas_shadow_external_package_def]) >>
  qpat_assum `run_grouped_lowering groups ips fall _ _ = _`
    (mp_then Any mp_tac grouped_internal_run_labels) >> simp[] >> strip_tac >>
  qpat_assum `run_grouped_lowering shadow_groups _ _ _ _ = _`
    (mp_then Any mp_tac grouped_internal_run_labels) >> simp[] >> strip_tac >>
  rename1 `compile_internal_fn_bodies ips start = ((),run_end)` >>
  rename1 `compile_internal_fn_bodies (MAP gas_shadow_internal_package ips)
    startS = ((),run_endS)` >>
  `gas_shadow_state start startS` by
    (qspecl_then [`MAP (package_external_group tops rp.rpol_target
                        T (K global_nonreentrant_slot)) exts`, `[]`, `fall`]
       mp_tac (Q.INST [`sd` |-> `T`] gas_shadow_compile_generate_grouped_runtime) >>
     qpat_assum `Abbrev (shadow_groups = _)` (fn th =>
       simp[gas_shadow_compiles_def, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     disch_then (qspecl_then [`initial_compile_state "__entry"`,
       `initial_compile_state "__entry"`] mp_tac) >>
     simp[gas_shadow_state_refl]) >>
  rename1 `extract_context_with_internals "__entry" _ run_endS =
    SOME (shadow_unit.cu_context,shadow_data)` >>
  mp_tac (Q.INST [`is_ctor` |-> `F`, `name` |-> `"__entry"`, `raw` |-> `unit.cu_context`,
    `rawS` |-> `shadow_unit.cu_context`, `dataS` |-> `shadow_data`,
    `srcs` |-> `order_internals (runtime_internal_order tops ints) ints`,
    `keys` |-> `runtime_internal_order tops
      (ints : (function_mutability # bool # bool # string # (string # type) list #
               expr list # type # stmt list) list)`]
    shadow_body_inv_from_internal_runs) >>
  fs[Abbr `ips`, gas_shadow_unit_def] >>
  Cases_on `enriched` >> simp[PERM_order_runtime_internals]
QED

Theorem runtime_shadow_body_layout:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\
  lower_vyper_runtime_unit tops rp = SOME unit /\
  runtime_gas_shadow_unit tops rp = SOME shadow_unit ==>
  shadow_body_inv_with (\a b. ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b)))
    tops unit.cu_context shadow_unit.cu_context
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = packages` >> PairCases_on `packages` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor_src)` >>
  Cases_on `EXISTS external_has_defaults exts`
  >- (irule (SIMP_RULE bool_ss []
              (Q.INST [`enriched` |-> `T`] runtime_grouped_shadow_body_with_fixed)) >>
      simp[] >> qexists_tac `rp` >> simp[]) >>
  `~EXISTS external_has_defaults (FST (classify_functions tops))` by
    (qpat_assum `classify_functions tops = _`
       (fn classify => PURE_REWRITE_TAC [classify, pairTheory.FST]) >>
     first_assum ACCEPT_TAC) >>
  `gas_shadow_unit unit shadow_unit` by
    (drule_all runtime_gas_shadow_unit_exists >> simp[]) >>
  qpat_assum `lower_vyper_runtime_unit _ _ = _`
    (mp_tac o REWRITE_RULE [lower_vyper_runtime_unit_def]) >>
  simp[AllCaseEqs()] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_lowering sels packs ips fall rp 0 0 [] info "__entry"` >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels` by
    simp[Abbr `sels`, build_selectors_fn_labels] >>
  `EVERY (\p. isPREFIX "fn_" (FST p)) packs` by
    (simp[Abbr `packs`, EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
          package_external_fn_def, set_external_package_target_def] >>
     metis_tac[]) >>
  `EVERY (\p. isPREFIX "fn_" (FST p)) (MAP gas_shadow_external_package packs)` by
    (simp_tac bool_ss [EVERY_MAP, EVERY_MEM] >>
     qx_gen_tac `pkg` >> disch_tac >>
     qpat_assum `EVERY (\p. isPREFIX "fn_" (FST p)) packs`
       (mp_tac o REWRITE_RULE [EVERY_MEM]) >>
     disch_then (qspec_then `pkg` mp_tac) >>
     PairCases_on `pkg` >> simp[gas_shadow_external_package_def]) >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    simp[Abbr `ips`, package_internal_labels] >>
  `EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors (MAP gas_shadow_internal_package ips))` by
    metis_tac[gas_shadow_internal_fn_descriptors] >>
  `run_lowering sels (MAP gas_shadow_external_package packs)
      (MAP gas_shadow_internal_package ips) (OPTION_MAP gas_shadow_fallback_package fall)
      rp 0 0 [] info "__entry" = SOME shadow_unit` by
    (qpat_x_assum `runtime_gas_shadow_unit _ _ = _` mp_tac >>
     simp[runtime_gas_shadow_unit_def, Abbr `sels`, Abbr `packs`, Abbr `ips`,
       Abbr `fall`, Abbr `info`]) >>
  qpat_assum `run_lowering sels packs ips fall _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_internal_run_labels) >> simp[] >> strip_tac >>
  qpat_assum `run_lowering sels (MAP gas_shadow_external_package packs) _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_internal_run_labels) >> simp[] >> strip_tac >>
  rename1 `compile_internal_fn_bodies ips start = ((),run_end)` >>
  rename1 `compile_internal_fn_bodies (MAP gas_shadow_internal_package ips)
    startS = ((),run_endS)` >>
  `gas_shadow_state start startS` by
    (mp_tac (Q.SPECL [`sels`, `packs`, `[]`, `fall`, `Linear`, `0`, `0`, `[]`, `info`]
       gas_shadow_compile_generate_runtime) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`initial_compile_state "__entry"`,
       `initial_compile_state "__entry"`] mp_tac) >> simp[gas_shadow_state_refl]) >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    fs[gas_shadow_unit_def] >>
  rename1 `extract_context_with_internals "__entry" _ run_endS =
    SOME (shadow_unit.cu_context,shadow_data)` >>
  mp_tac (Q.INST [`is_ctor` |-> `F`, `name` |-> `"__entry"`, `raw` |-> `unit.cu_context`,
    `rawS` |-> `shadow_unit.cu_context`, `dataS` |-> `shadow_data`,
    `srcs` |-> `order_internals (runtime_internal_order tops ints) ints`,
    `keys` |-> `runtime_internal_order tops
      (ints : (function_mutability # bool # bool # string # (string # type) list #
               expr list # type # stmt list) list)`, `enriched` |-> `T`]
    shadow_body_inv_from_internal_runs) >>
  simp[Abbr `ips`]
QED

Theorem runtime_grouped_shadow_body_with[local]:
  (enriched ==> supported_program tops) /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  lower_vyper_runtime_unit tops rp = SOME unit ==>
  ?shadow_unit. gas_shadow_unit unit shadow_unit /\
    shadow_body_inv_with
      (\a b. enriched ==> ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b)))
      tops unit.cu_context shadow_unit.cu_context
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = packages` >> PairCases_on `packages` >>
  drule_all runtime_gas_shadow_unit_exists >> strip_tac >>
  qexists_tac `shadow_unit` >> asm_rewrite_tac[] >>
  mp_tac (Q.INST [`tops` |-> `tops`, `rp` |-> `rp`, `unit` |-> `unit`,
                  `shadow_unit` |-> `shadow_unit`]
    runtime_grouped_shadow_body_with_fixed) >>
  fs[]
QED

Theorem runtime_grouped_shadow_body_layout:
  supported_program tops /\
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  lower_vyper_runtime_unit tops rp = SOME unit ==>
  ?shadow_unit. gas_shadow_unit unit shadow_unit /\
    shadow_body_inv_with
      (\a b. ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b)))
      tops unit.cu_context shadow_unit.cu_context
Proof
  MATCH_ACCEPT_TAC (SIMP_RULE bool_ss []
    (Q.INST [`enriched` |-> `T`] runtime_grouped_shadow_body_with))
QED

Theorem deploy_shadow_body_layout:
  !tops am tx rp bc unit shadow_unit exts ints fb cf ce args pay nr key trans ctor_body ret.
    deploy_source_ok tops am tx /\ lower_vyper_deploy_unit tops rp bc = SOME unit /\
    classify_functions tops = (exts,ints,fb,SOME cf) /\
    set_constructor_package_target rp.rpol_target
      (package_constructor tops T (K global_nonreentrant_slot) cf) =
      (ce,args,pay,nr,key,trans,ctor_body,ret) /\
    run_deploy_lowering T rp bc (imm_len tops) args 0
      (MAP gas_shadow_internal_package
        (MAP (set_internal_package_target rp.rpol_target o
          package_internal_fn tops T (K global_nonreentrant_slot) T
            (imm_len tops))
          (order_internals (deploy_internal_order (SOME cf) ints) ints)))
      (gas_shadow_env T ce) (MAP gas_shadow_stmt ctor_body) pay nr key trans "__deploy" =
      SOME shadow_unit ==>
    shadow_body_inv_with (\a b. ALL_DISTINCT (b.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks a b)))
    tops unit.cu_context shadow_unit.cu_context
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `srcs = order_internals (deploy_internal_order (SOME cf) ints) ints` >>
  qabbrev_tac `ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn tops T (K global_nonreentrant_slot) T (imm_len tops)) srcs` >>
  `run_deploy_lowering T rp bc (imm_len tops) args 0 ips
    ce ctor_body pay nr key trans "__deploy" = SOME unit` by
    (qpat_assum `lower_vyper_deploy_unit _ _ _ = _`
       (mp_tac o REWRITE_RULE [lower_vyper_deploy_unit_def]) >>
     simp[GSYM imm_len_def, Abbr `ips`, Abbr `srcs`] >>
     rw[AllCaseEqs()]) >>
  qpat_assum `run_deploy_lowering T _ _ _ _ _ ips _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac deploy_internal_run_labels) >> simp[] >> strip_tac >>
  qpat_assum `run_deploy_lowering T _ _ _ _ _ (MAP gas_shadow_internal_package ips)
      _ _ _ _ _ _ _ = _` (mp_then Any mp_tac deploy_internal_run_labels) >>
  strip_tac >>
  rename1 `compile_internal_fn_bodies ips start = ((),run_end)` >>
  rename1 `compile_internal_fn_bodies (MAP gas_shadow_internal_package ips)
    startS = ((),run_endS)` >>
  rename1 `extract_context_with_internals "__deploy" ips run_end = SOME (raw,data)` >>
  rename1 `extract_context_with_internals "__deploy" (MAP gas_shadow_internal_package ips)
    run_endS = SOME (rawS,dataS)` >>
  `gas_shadow_state start startS` by
    (mp_tac (Q.SPECL [`T`, `LENGTH (bc : word8 list)`, `imm_len tops`, `args`, `0`, `[]`, `ce`,
       `ctor_body`, `pay`, `nr`, `key`, `trans`]
       (Q.INST [`sd` |-> `T`] gas_shadow_compile_generate_deploy)) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`initial_compile_state "__deploy"`,
       `initial_compile_state "__deploy"`] mp_tac) >> simp[gas_shadow_state_refl]) >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    (mp_tac (Q.SPECL [`T`, `rp`, `bc`, `imm_len tops`, `args`, `0`, `ips`, `ce`,
       `ctor_body`, `pay`, `nr`, `key`, `trans`, `"__deploy"`] gas_shadow_run_deploy_lowering) >>
     simp[optionTheory.OPTREL_def, gas_shadow_unit_def]) >>
  mp_tac (Q.INST [`is_ctor` |-> `T`, `name` |-> `"__deploy"`,
      `keys` |-> `deploy_internal_order
        (SOME (cf : function_mutability # bool # bool # string # (string # type) list #
                    expr list # type # stmt list))
        (ints : (function_mutability # bool # bool # string # (string # type) list #
                 expr list # type # stmt list) list)`, `enriched` |-> `T`]
    shadow_body_inv_from_internal_runs) >>
  fs[deploy_source_ok_def, install_immutable_reservation_def, Abbr `srcs`]
QED

Theorem runtime_shadow_body_inv:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\
  lower_vyper_runtime_unit tops rp = SOME unit /\
  runtime_gas_shadow_unit tops rp = SOME shadow_unit ==>
  shadow_body_inv tops unit.cu_context shadow_unit.cu_context
Proof
  metis_tac[runtime_shadow_body_layout, shadow_body_inv_with_forget]
QED

Theorem runtime_grouped_shadow_body_inv:
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  lower_vyper_runtime_unit tops rp = SOME unit ==>
  ?shadow_unit. gas_shadow_unit unit shadow_unit /\
    shadow_body_inv tops unit.cu_context shadow_unit.cu_context
Proof
  MATCH_ACCEPT_TAC (SIMP_RULE bool_ss [shadow_body_inv_with_plain]
    (Q.INST [`enriched` |-> `F`] runtime_grouped_shadow_body_with))
QED

Theorem deploy_shadow_body_inv:
  !tops am tx rp bc unit shadow_unit exts ints fb cf ce args pay nr key trans ctor_body ret.
    deploy_source_ok tops am tx /\ lower_vyper_deploy_unit tops rp bc = SOME unit /\
    classify_functions tops = (exts,ints,fb,SOME cf) /\
    set_constructor_package_target rp.rpol_target
      (package_constructor tops T (K global_nonreentrant_slot) cf) =
      (ce,args,pay,nr,key,trans,ctor_body,ret) /\
    run_deploy_lowering T rp bc (imm_len tops) args 0
      (MAP gas_shadow_internal_package
        (MAP (set_internal_package_target rp.rpol_target o
          package_internal_fn tops T (K global_nonreentrant_slot) T
            (imm_len tops))
          (order_internals (deploy_internal_order (SOME cf) ints) ints)))
      (gas_shadow_env T ce) (MAP gas_shadow_stmt ctor_body) pay nr key trans "__deploy" =
      SOME shadow_unit ==>
    shadow_body_inv tops unit.cu_context shadow_unit.cu_context
Proof
  rpt gen_tac >> strip_tac >> drule_all deploy_shadow_body_layout >>
  disch_then (irule o MATCH_MP shadow_body_inv_with_forget)
QED

(* Two modules can declare the same internal name and lower to distinct labels. *)
Theorem two_module_unit_lowers[local]:
  mods = [(NONE,[FunctionDecl Internal Pure F F "foo" [] [] NoneT [Pass]]);
          (SOME 1,[FunctionDecl Internal Pure F F "foo" [] [] NoneT [Pass]])] ==>
  ?unit main lib.
    lower_vyper_runtime_unit_mods mods []
      <| rpol_target := all_capabilities;
         rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |> = SOME unit /\
    lookup_function (internal_fn_label 0 "foo" [] F)
      unit.cu_context.ctx_functions = SOME main /\
    lookup_function (internal_fn_label 1 "1.foo" [] F)
      unit.cu_context.ctx_functions = SOME lib
Proof
  strip_tac >> gvs[] >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[]
QED

Theorem foo_supported[local]:
  supported_program [FunctionDecl Internal Pure F F "foo" [] [] NoneT [Pass]]
Proof
  simp[supported_program_def, supported_declaration_headers_def,
       supported_declaration_header_def, supported_declaration_names_def,
       supported_function_return_def, supported_internal_function_names_def,
       supported_declaration_body_def, supported_function_header_names_def,
       supported_function_bindings_def, supported_function_body_def,
       supported_function_names_def, supported_event_names_def,
       supported_selectors_distinct_def, classify_functions_def, classify_function_def,
       public_getters_def, public_getter_def, build_selectors_def, module_consts_env_def] >>
  simp[supported_stmt_def, supported_stmt_bindings_def, supported_stmts_expr_exists_list,
       supported_stmt_expr_exists_def, body_stmts_safe_iff, int_calls_stmt_def,
       supported_pure_expr_def]
QED

Theorem two_module_unit_invariants[local]:
  tops = [FunctionDecl Internal Pure F F "foo" [] [] NoneT [Pass]] /\
  mods = [(NONE,tops); (SOME 1,tops)] ==>
  ?ctx cenv cx main lib.
    contract_inv mods [] ctx cenv cx /\
    module_body_inv mods (SOME 1) tops cenv cx /\
    ~cx.in_deploy /\
    lookup_function (internal_fn_label 0 "foo" [] F)
      ctx.ctx_functions = SOME main /\
    lookup_function (internal_fn_label 1 "1.foo" [] F)
      ctx.ctx_functions = SOME lib
Proof
  strip_tac >>
  `supported_module_headers [FunctionDecl Internal Pure F F "foo" [] [] NoneT [Pass]]` by
    metis_tac[foo_supported, supported_program_module_headers] >>
  `mods = [(NONE,[FunctionDecl Internal Pure F F "foo" [] [] NoneT [Pass]]);
           (SOME 1,[FunctionDecl Internal Pure F F "foo" [] [] NoneT [Pass]])]`
    by fs[] >>
  drule two_module_unit_lowers >> strip_tac >>
  qabbrev_tac `ce = build_compile_env_unit mods (SOME 1) Internal Pure "foo"
    [] NoneT [Pass] T` >>
  `cenv_module_pins_mods mods ce` by
    simp[NoAsms, Abbr `ce`, build_compile_env_unit_def, cenv_module_pins_mods_def,
         pairTheory.ELIM_UNCURRY] >>
  qexists_tac `unit.cu_context` >>
  qexists_tac `ce` >>
  qexists_tac `(ARB:evaluation_context) with
    <| in_deploy := F; sources := [((ARB:evaluation_context).txn.target,mods)] |>` >>
  qexistsl_tac [`main`, `lib`] >>
  simp[contract_inv_def, module_body_inv_def, get_tenv_def] >>
  rpt conj_tac >>
  simp[NoAsms, Abbr `ce`, build_compile_env_unit_def, pairTheory.ELIM_UNCURRY] >>
  gvs[] >>
  simp[foo_supported, toplevel_vtype_keys_toplevel_def, make_struct_fields_map_mods_def,
       build_struct_fields_map_mods_def, build_struct_fields_map_src_def] >>
  simp[immutable_section_layout_mods_def, immutable_region_mods_def,
       imm_len_mods_def, ALOOKUP_def, AllCaseEqs(),
       add_module_var_locations_mods_def, add_module_var_locations_src_def,
       add_immutable_locations_unit_def, add_annotated_immutables_mods_def,
       add_annotated_immutables_src_def, compute_immutables_len_unit_def,
       annotated_immutables_len_def] >>
  rpt strip_tac >> gvs[foo_supported, toplevel_vtype_keys_toplevel_def,
    function_mutability_ok_def, stmt_mutability_ok_def, listTheory.APPEND_EQ_SING,
    linked_body_calls_resolved_def, function_int_calls_def,
    supported_declaration_body_def, supported_function_body_def,
    supported_stmt_bindings_def, supported_stmt_def, body_stmts_safe_iff, body_stmt_safe_def,
    supported_stmt_expr_exists_def, int_calls_stmt_def]
  >- (qexistsl_tac [`<| rpol_target := all_capabilities;
                     rpol_frontend_dispatch := Linear;
                     rpol_final_assembly := FAP_Optimize |>`, `unit`] >>
     simp[EQ_SYM_EQ]) >>
  rpt strip_tac >> gvs[AllCaseEqs(), function_mutability_ok_def,
    stmt_mutability_ok_def, function_int_calls_def, supported_declaration_body_def,
    supported_function_body_def, supported_stmt_def, body_stmts_safe_iff,
    body_stmt_safe_def, supported_stmt_bindings_def, supported_stmt_expr_exists_def,
    int_calls_stmt_def, int_calls_expr_def, supported_pure_expr_def, LET_THM]
QED

Theorem linked_two_module_internal_code:
  tops = [FunctionDecl Internal Pure F F "foo" [] [] NoneT [Pass]] /\
  mods = [(NONE,tops); (SOME 1,tops)] ==>
  ?ctx cenv cx main lib entry final.
    contract_inv mods [] ctx cenv cx /\
    module_body_inv mods (SOME 1) tops cenv cx /\
    immutable_section_layout_mods mods cenv /\
    ~cx.in_deploy /\
    lookup_function (internal_fn_label 0 "foo" [] F)
      ctx.ctx_functions = SOME main /\
    lookup_function (internal_fn_label 1 "1.foo" [] F)
      ctx.ctx_functions = SOME lib /\
    fn_has_code entry final lib /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) lib.fn_blocks)
Proof
  strip_tac >> drule_all two_module_unit_invariants >> strip_tac >>
  `immutable_section_layout_mods mods cenv` by
    metis_tac[body_inv_immutable_section_layout_mods] >>
  `nsid_to_string (SOME 1,"foo") = "1.foo" /\
    build_func_ids_mods 0 mods "1.foo" = 1` by
    (qpat_x_assum `mods = _` SUBST1_TAC >>
     qpat_x_assum `tops = _` SUBST1_TAC >> EVAL_TAC >> simp[]) >>
  `MEM (FunctionDecl Internal Pure F F "foo" [] [] NoneT [Pass]) tops` by simp[] >>
  qpat_x_assum `mods = _` kall_tac >>
  qpat_x_assum `tops = _` kall_tac >>
  `lookup_function
      (internal_fn_label
        (build_func_ids_mods 0 mods (nsid_to_string (SOME 1,"foo")))
        (nsid_to_string (SOME 1,"foo")) (MAP SND ([] : (string # type) list))
        cx.in_deploy) ctx.ctx_functions = SOME lib` by simp[] >>
  drule_all body_inv_selected_internal_code_mods >> strip_tac >>
  qexistsl_tac [`ctx`, `cenv`, `cx`, `main`, `lib`, `entry`, `final`] >>
  simp[]
QED

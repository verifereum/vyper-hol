Theory bodyFullShadowBodyInvLowering
Ancestors
  bodyFullShadowBodyInv bodyFullShadowInternalCode gasShadowRunLowering
  gasShadowDeployRunner gasShadowModuleDefs gasShadow gasShadowUnit
  gasShadowState gasShadowShape gasShadowRuntime gasShadowDeploy
  gasShadowUnitExtract gasShadowInternal
  compileVyper vyperCompiler compileEnv moduleLowering immSectionDead
  loweringShapeProps loweringShapeDefs loweringShapeSource
  ctorDeployLoweringCode ctorDeployLoweringDefs ctorDeployDefs ctorGeneratorShape
  supportedProgram supportedDecls constSubst venomInst venomWf list rich_list
  venomCompilerTypes sorting

(* The generator run with no internal packages ends just before the suffix. *)
Theorem compile_runtime_internal_suffix[local]:
  compile_generate_runtime sels exts ips fb dispatch buckets metadata dense info st =
  compile_internal_fn_bodies ips
    (SND (compile_generate_runtime sels exts [] fb dispatch buckets metadata dense info st))
Proof
  simp[compile_generate_runtime_def, LET_THM, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem compile_deploy_internal_suffix[local]:
  compile_generate_deploy T code_size cap args data_size ips ce ss pay nr key trans st =
  compile_internal_fn_bodies ips
    (SND (compile_generate_deploy T code_size cap args data_size [] ce ss pay nr key trans st))
Proof
  simp[compile_generate_deploy_def, LET_THM, compile_internal_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

Theorem runtime_internal_run[local]:
  run_lowering sels exts ips fb rp buckets metadata dense info "__entry" = SOME unit /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY external_fn_shape_ok exts /\ fallback_shape_ok fb ==>
  ?start run_end data.
    compile_generate_runtime sels exts [] fb Linear buckets metadata dense info
      (initial_compile_state "__entry") = ((),start) /\
    compile_internal_fn_bodies ips start = ((),run_end) /\
    extract_context_with_internals "__entry" ips run_end =
      SOME (unit.cu_context,data) /\
    lowering_context_ok unit.cu_context /\
    shape_state start /\ all_blocks start <> [] /\
    (HD (all_blocks start)).bb_label = "__entry" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start)))
Proof
  strip_tac >>
  Cases_on `compile_generate_runtime sels exts [] fb Linear buckets
    metadata dense info (initial_compile_state "__entry")` >>
  rename1 `compile_generate_runtime _ _ [] _ _ _ _ _ _ _ = (u,start)` >>
  Cases_on `u` >>
  mp_tac (Q.SPECL [`sels`, `exts`, `[]`, `fb`, `buckets`, `metadata`, `dense`, `info`,
    `start`] compile_generate_runtime_shape) >>
  simp[internal_fn_descriptors_def] >> strip_tac >> gvs[] >>
  `lowering_policy_ok rp` by fs[run_lowering_def, AllCaseEqs()] >>
  `rp.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  `compile_generate_runtime sels exts ips fb Linear buckets metadata dense
     info (initial_compile_state "__entry") = compile_internal_fn_bodies ips start` by
    (once_rewrite_tac[compile_runtime_internal_suffix] >> simp[]) >>
  Cases_on `compile_internal_fn_bodies ips start` >>
  rename1 `compile_internal_fn_bodies ips start = (u,run_end)` >>
  Cases_on `u` >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl_tac [`start`, `run_end`] >> simp[]
QED

Theorem deploy_internal_run[local]:
  run_deploy_lowering T rp bc cap args data_size ips ce ss pay nr key trans
    "__deploy" = SOME unit /\
  cenv_static_ok ce /\ ce.ce_return_pc = NONE /\
  ~supported_stmts_expr_exists expr_shape_root ss ==>
  ?start run_end raw data.
    compile_generate_deploy T (LENGTH (bc : word8 list)) cap args data_size [] ce ss pay nr key trans
      (initial_compile_state "__deploy") = ((),start) /\
    compile_internal_fn_bodies ips start = ((),run_end) /\
    extract_context_with_internals "__deploy" ips run_end = SOME (raw,data) /\
    unit.cu_context = install_immutable_reservation cap raw /\
    lowering_context_ok unit.cu_context /\
    shape_state start /\ all_blocks start <> [] /\
    (HD (all_blocks start)).bb_label = "__deploy" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start)))
Proof
  strip_tac >>
  Cases_on `compile_generate_deploy T (LENGTH (bc : word8 list)) cap args data_size [] ce ss
    pay nr key trans (initial_compile_state "__deploy")` >>
  rename1 `compile_generate_deploy _ _ _ _ _ [] _ _ _ _ _ _ _ = (u,start)` >>
  Cases_on `u` >>
  mp_tac (Q.SPECL [`T`, `LENGTH (bc : word8 list)`, `cap`, `args`, `data_size`, `[]`, `ce`, `ss`,
    `pay`, `nr`, `key`, `trans`, `start`] compile_generate_deploy_shape) >>
  simp[internal_fn_descriptors_def] >> strip_tac >> gvs[] >>
  `lowering_policy_ok rp` by fs[run_deploy_lowering_def, AllCaseEqs()] >>
  `compile_generate_deploy T (LENGTH (bc : word8 list)) cap args data_size ips ce ss
     pay nr key trans (initial_compile_state "__deploy") =
     compile_internal_fn_bodies ips start` by
    (once_rewrite_tac[compile_deploy_internal_suffix] >> simp[]) >>
  Cases_on `compile_internal_fn_bodies ips start` >>
  rename1 `compile_internal_fn_bodies ips start = (u,run_end)` >>
  Cases_on `u` >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qexistsl_tac [`start`, `run_end`] >> simp[]
QED

Theorem internal_fn_label_mode[local]:
  internal_fn_label id fname tys mode = internal_fn_label id' fname' tys' mode' ==>
  mode = mode'
Proof
  Cases_on `mode` >> Cases_on `mode'` >> simp[] >>
  disch_then (mp_tac o Q.AP_TERM `\(s:string). HD (REVERSE s)`) >>
  simp[internal_fn_label_def, REVERSE_APPEND]
QED

Theorem packaged_internal_mode[local]:
  ips = MAP (set_internal_package_target target o
    package_internal_fn tops T (K global_nonreentrant_slot) is_ctor cap)
      (srcs : (function_mutability # bool # bool # string #
        (string # type) list # expr list # type # stmt list) list) /\
  name = (if is_ctor then "__deploy" else "__entry") /\
  extract_context_with_internals name ips run_end = SOME (raw,data) /\
  lookup_function (internal_fn_label id fname tys mode) raw.ctx_functions =
    SOME callee ==> mode = is_ctor
Proof
  strip_tac >>
  `MEM (internal_fn_label id fname tys mode)
    (name :: MAP FST (internal_fn_descriptors ips))` by
    metis_tac[venomInstTheory.lookup_function_mem, extract_context_internal_names] >>
  qpat_x_assum `MEM _ (_::_)` mp_tac >>
  simp[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
       internal_fn_descriptors_MAP_package_internal_fn, MEM_MAP,
       pairTheory.EXISTS_PROD] >>
  strip_tac
  >- (Cases_on `is_ctor` >> fs[internal_fn_label_def]) >>
  qpat_x_assum `_ = source_internal_fn_descriptor _ _ _`
    (mp_tac o Q.AP_TERM `FST`) >>
  simp[] >> metis_tac[internal_fn_label_mode]
QED

Theorem shadow_body_inv_from_internal_runs[local]:
  supported_program tops /\
  (if is_ctor then lower_vyper_deploy_unit tops rp bc = SOME unit
   else lower_vyper_runtime_unit tops rp = SOME unit) /\
  name = (if is_ctor then "__deploy" else "__entry") /\
  PERM srcs (FST (SND (classify_functions tops))) /\
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
  gas_shadow_state start startS /\ shape_state start /\ shape_state startS /\
  all_blocks start <> [] /\ all_blocks startS <> [] /\
  (HD (all_blocks start)).bb_label = name /\
  (HD (all_blocks startS)).bb_label = name /\
  EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks start))) /\
  EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks startS))) ==>
  shadow_body_inv tops unit.cu_context shadow_unit.cu_context
Proof
  strip_tac >>
  simp[shadow_body_inv_def] >> rpt gen_tac >> strip_tac >>
  rename1 `lookup_function (internal_fn_label _ fname _ mode) _ = SOME callee` >>
  `mode = is_ctor` by
    (mp_tac (Q.INST [`target` |-> `rp.rpol_target`,
      `cap` |-> `if is_ctor then imm_len tops else 0`, `id` |-> `build_func_ids 0 tops fname`,
      `tys` |-> `MAP SND (args : (string # type) list)`] packaged_internal_mode) >> fs[]) >>
  qpat_x_assum `mode = is_ctor` SUBST_ALL_TAC >>
  `module_consts_env tops [] = []` by
    metis_tac[supported_program_def, supported_declaration_headers_def,
      supported_headers_module_consts_env] >>
  `MEM (mut,nr,rr,fname,args,dflts,ret,ss) srcs` by
    (qpat_assum `PERM srcs _` (mp_tac o MATCH_MP PERM_MEM_EQ) >>
     disch_then (qspec_then `(mut,nr,rr,fname,args,dflts,ret,ss)` SUBST1_TAC) >>
     simp[MEM_classify_internal]) >>
  `EVERY internal_fn_shape_ok ips /\
   EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
   ALL_DISTINCT (MAP FST (internal_fn_descriptors ips))` by
    (mp_tac (Q.SPECL [`tops`, `rp.rpol_target`, `T`,
      `K global_nonreentrant_slot`, `is_ctor`, `if is_ctor then imm_len tops else 0`,
      `srcs`, `ips`] deploy_internal_package_certificates) >> simp[]) >>
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
      (if is_ctor then imm_len tops else 0) (mut,nr,rr,fname,args,dflts,ret,ss))` >>
  `MEM pkg ips` by
    (simp[MEM_MAP] >> qexists_tac `(mut,nr,rr,fname,args,dflts,ret,ss)` >>
     simp[Abbr `pkg`]) >>
  `EVERY internal_fn_shape_ok (MAP gas_shadow_internal_package ips)` by
    (simp[EVERY_MAP, EVERY_MEM] >> metis_tac[gas_shadow_internal_fn_shape_ok, EVERY_MEM]) >>
  qpat_x_assum `ips = MAP _ srcs` kall_tac >>
  qpat_x_assum `MEM pkg ips` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  rename1 `ips = xs ++ pkg::ys` >>
  PairCases_on `pkg` >>
  rename1 `Abbrev ((label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt) = _)` >>
  `set_internal_package_target rp.rpol_target
    (package_internal_fn tops T (K global_nonreentrant_slot) is_ctor
      (if is_ctor then imm_len tops else 0) (mut,nr,rr,fname,args,dflts,ret,ss)) =
    (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt)` by
    (qpat_assum `Abbrev ((label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,
        compiled_ss,rt) = _)` (mp_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >> simp[]) >>
  `label = internal_fn_label (build_func_ids 0 tops fname) fname
     (MAP SND args) is_ctor /\ compiled_ss = ss` by
    (qpat_assum `set_internal_package_target _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [package_internal_fn_def, LET_THM,
       set_internal_package_target_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`pkg` |-> `(label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,compiled_ss,rt)`,
    `nr` |-> `nr'`, `ss` |-> `compiled_ss`, `ctx` |-> `raw`, `sctx` |-> `rawS`,
    `sdata` |-> `dataS`, `sips` |-> `MAP gas_shadow_internal_package ips`]
    (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] selected_internal_shadow_code)) >>
  impl_tac >-
    (fs[lowering_context_ok_def, ctx_fn_names_def, fn_labels_def,
        ctx_inst_ids_distinct_def] >>
     Cases_on `is_ctor` >> gvs[EVERY_MAP, EVERY_MEM, gas_shadow_internal_fn_shape_ok]) >>
  strip_tac >>
  qexistsl_tac [`rp`, `unit`, `label`, `ce`, `params`, `has_rb`, `nr'`, `key`,
    `trans`, `view`, `ctor`, `ilen`, `rt`] >>
  gs[imm_len_def, bool_case_eq, lowering_context_ok_def] >>
  metis_tac[]
QED

Theorem runtime_shadow_body_inv:
  supported_program tops /\ lower_vyper_runtime_unit tops rp = SOME unit /\
  runtime_gas_shadow_unit tops rp = SOME shadow_unit ==>
  shadow_body_inv tops unit.cu_context shadow_unit.cu_context
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = packages` >> PairCases_on `packages` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor_src)` >>
  `~EXISTS external_has_defaults exts` by
    (mp_tac (Q.SPEC `tops` supported_program_no_external_defaults) >> simp[]) >>
  `runtime_bodies_shape_ok tops` by
    metis_tac[supported_program_runtime_bodies_shape_ok] >>
  qpat_assum `lower_vyper_runtime_unit _ _ = _`
    (mp_tac o REWRITE_RULE [lower_vyper_runtime_unit_def]) >>
  simp[AllCaseEqs()] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_lowering sels packs ips fall rp 0 0 [] info "__entry"` >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels` by
    simp[Abbr `sels`, build_selectors_fn_labels] >>
  `EVERY external_fn_shape_ok packs` by
    (simp[Abbr `packs`, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_external_fn_shape_ok >> gs[]) >>
  `fallback_shape_ok fall` by
    (qspecl_then [`tops`, `T`, `K global_nonreentrant_slot`, `rp.rpol_target`]
       mp_tac package_fallback_fn_shape_ok >> gs[Abbr `fall`]) >>
  `run_lowering sels (MAP gas_shadow_external_package packs)
      (MAP gas_shadow_internal_package ips) (OPTION_MAP gas_shadow_fallback_package fall)
      rp 0 0 [] info "__entry" = SOME shadow_unit` by
    (qpat_x_assum `runtime_gas_shadow_unit _ _ = _` mp_tac >>
     simp[runtime_gas_shadow_unit_def, Abbr `sels`, Abbr `packs`, Abbr `ips`,
       Abbr `fall`, Abbr `info`]) >>
  `EVERY external_fn_shape_ok (MAP gas_shadow_external_package packs) /\
    fallback_shape_ok (OPTION_MAP gas_shadow_fallback_package fall)` by
    (fs[EVERY_MAP, EVERY_MEM] >>
     metis_tac[gas_shadow_external_fn_shape_ok, gas_shadow_fallback_shape_ok]) >>
  qpat_assum `run_lowering sels packs ips fall _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_internal_run) >> simp[] >> strip_tac >>
  qpat_assum `run_lowering sels (MAP gas_shadow_external_package packs) _ _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_internal_run) >> simp[] >> strip_tac >>
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
    (mp_tac (Q.SPECL [`sels`, `packs`, `ips`, `fall`, `rp`, `0`, `0`, `[]`, `info`,
       `"__entry"`] gas_shadow_run_lowering) >>
     simp[optionTheory.OPTREL_def, gas_shadow_unit_def]) >>
  rename1 `extract_context_with_internals "__entry" _ run_endS =
    SOME (shadow_unit.cu_context,shadow_data)` >>
  mp_tac (Q.INST [`is_ctor` |-> `F`, `name` |-> `"__entry"`, `raw` |-> `unit.cu_context`,
    `rawS` |-> `shadow_unit.cu_context`, `dataS` |-> `shadow_data`,
    `srcs` |-> `order_internals (runtime_internal_order tops ints) ints`]
    shadow_body_inv_from_internal_runs) >>
  simp[Abbr `ips`, PERM_order_runtime_internals]
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
      ce (MAP gas_shadow_stmt ctor_body) pay nr key trans "__deploy" =
      SOME shadow_unit ==>
    shadow_body_inv tops unit.cu_context shadow_unit.cu_context
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
  drule_all deploy_constructor_package_shape >> strip_tac >>
  qpat_assum `run_deploy_lowering T _ _ _ _ _ ips _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac deploy_internal_run) >> simp[] >> strip_tac >>
  qpat_assum `run_deploy_lowering T _ _ _ _ _ (MAP gas_shadow_internal_package ips)
      _ _ _ _ _ _ _ = _` (mp_then Any mp_tac deploy_internal_run) >>
  simp[gas_shadow_shape_stmts_exists] >> strip_tac >>
  rename1 `compile_internal_fn_bodies ips start = ((),run_end)` >>
  rename1 `compile_internal_fn_bodies (MAP gas_shadow_internal_package ips)
    startS = ((),run_endS)` >>
  rename1 `extract_context_with_internals "__deploy" ips run_end = SOME (raw,data)` >>
  rename1 `extract_context_with_internals "__deploy" (MAP gas_shadow_internal_package ips)
    run_endS = SOME (rawS,dataS)` >>
  `gas_shadow_state start startS` by
    (mp_tac (Q.SPECL [`T`, `LENGTH (bc : word8 list)`, `imm_len tops`, `args`, `0`, `[]`, `ce`,
       `ctor_body`, `pay`, `nr`, `key`, `trans`] gas_shadow_compile_generate_deploy) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`initial_compile_state "__deploy"`,
       `initial_compile_state "__deploy"`] mp_tac) >> simp[gas_shadow_state_refl]) >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    (mp_tac (Q.SPECL [`T`, `rp`, `bc`, `imm_len tops`, `args`, `0`, `ips`, `ce`,
       `ctor_body`, `pay`, `nr`, `key`, `trans`, `"__deploy"`] gas_shadow_run_deploy_lowering) >>
     simp[optionTheory.OPTREL_def, gas_shadow_unit_def]) >>
  mp_tac (Q.INST [`is_ctor` |-> `T`, `name` |-> `"__deploy"`]
    shadow_body_inv_from_internal_runs) >>
  fs[deploy_source_ok_def, install_immutable_reservation_def, Abbr `srcs`,
     PERM_order_deploy_internals]
QED

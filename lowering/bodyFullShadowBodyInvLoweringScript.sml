Theory bodyFullShadowBodyInvLowering
Ancestors
  bodyFullShadowBodyInv bodyFullShadowInternalCode gasShadowRunLowering
  gasShadowDeployRunner gasShadowModuleDefs gasShadow gasShadowUnit
  gasShadowState gasShadowShape gasShadowRuntime gasShadowDeploy
  gasShadowUnitExtract gasShadowInternal
  compileVyper vyperCompiler compileEnv moduleLowering immSectionDead
  loweringShapeProps loweringShapeDefs loweringShapeSource
  ctorDeployLoweringCode ctorDeployLoweringDefs ctorDeployDefs ctorGeneratorShape
  ctorDeployEntryLabels
  supportedProgram supportedDecls constSubst venomInst venomWf list rich_list
  venomCompilerTypes sorting constSubstStmtsPreserve supportedNameRoot
  vyperTypeContractStaticMaps e2eDeployDefs bodySim ctorDeployShape
  bodyInvSplit bodyInvModuleProps bodySimModsProps
  bodyInternalFunctionIntervalProps internalBlockPackagingProps
  compileUnit constSubstMods groupedInternalLabels intCallLookup alist pair
  externalEntryShape externalEntryChecks loweringShapeRules
  context emitHelper stmtLowering
  vyperGetter publicGetterProps supportedNames supportedStmts supportedStmtTraverse
  supportedExprs vyperContext vyperTypeContract vyperTypeCallGraph typedCopyDomain
Libs
  monadsyntax

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

Theorem extract_context_internal_code_by_labels[local]:
  extract_context_with_internals name packages final = SOME (ctx,data) /\
  ALL_DISTINCT (MAP (\f. f.fn_name) ctx.ctx_functions) /\
  EVERY (\f. ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks)) ctx.ctx_functions /\
  compile_internal_fn_bodies packages start = ((),final) /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors packages) /\
  EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start) /\
  MEM (label,ce,params,has_buf,nr,key,trans,view,ctor,ilen,ss,ret) packages /\
  lookup_function label ctx.ctx_functions = SOME func ==>
  ?before old entry after.
    new_block label before = (old,entry) /\
    compile_internal_function ce params has_buf nr key trans view ctor ilen
      ss ret entry = ((),after) /\
    fn_has_code entry after func /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks)
Proof
  strip_tac >> drule compile_internal_fn_bodies_label_segments >> strip_tac >>
  drule extract_context_internal_names >> strip_tac >>
  `ALL_DISTINCT (MAP FST (internal_fn_descriptors packages))` by fs[] >>
  `EVERY (\d. ~isPREFIX "@" (FST d) /\
       ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks start)))
       (internal_fn_descriptors packages)` by
    (`!lbl. isPREFIX "@" lbl ==> ~internal_label_ok lbl` by
       (Cases >> simp[internal_label_ok_def]) >>
     fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `LIST_REL
      (\d seg. seg <> [] /\ (HD seg).bb_label = FST d /\
        EVERY (\bb. isPREFIX "@" bb.bb_label) (TL seg))
      (internal_fn_descriptors packages) segments` by
    (rewrite_tac[internal_fn_descriptors_map, LIST_REL_MAP1] >>
     irule LIST_REL_mono >> goal_assum (drule_at Any) >>
     simp[combinTheory.o_DEF, pairTheory.FORALL_PROD]) >>
  drule_all (Q.SPECL [`internal_fn_descriptors packages`, `segments`,
    `all_blocks start`, `isPREFIX "@"`] package_internal_blocks_separated_segments) >>
  strip_tac >>
  qpat_x_assum `extract_context_with_internals _ _ _ = _` mp_tac >>
  simp[extract_context_with_internals_def, GSYM all_blocks_def] >>
  strip_tac >>
  qpat_x_assum `MEM (label,ce,_,_,_,_,_,_,_,_,_,_) packages`
    (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
  rename1 `_ = EL i packages` >>
  qpat_x_assum `LIST_REL _ packages segments` mp_tac >>
  simp[LIST_REL_EL_EQN] >> strip_tac >>
  qpat_x_assum `!n. n < LENGTH packages ==> _` (qspec_then `i` mp_tac) >>
  qpat_x_assum `(label,ce,_,_,_,_,_,_,_,_,_,_) = EL i packages`
    (assume_tac o SYM) >>
  simp[] >> strip_tac >>
  qabbrev_tac `selected = mk_internal_function label (EL i segments)
    has_buf ce.ce_returns_count` >>
  `MEM selected ctx.ctx_functions` by
    (qpat_x_assum `mk_venom_context _ _ = ctx` (SUBST1_TAC o SYM) >>
     simp[mk_venom_context_def, Abbr `selected`] >>
     disj2_tac >> simp[MEM_EL, internal_fn_descriptors_map, LENGTH_MAP2] >>
     qexists_tac `i` >>
     simp[EL_MAP2, EL_MAP, arithmeticTheory.MIN_DEF]) >>
  `selected = func` by
    (drule_all lookup_function_distinct_mem >>
     simp[Abbr `selected`, mk_internal_function_metadata]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) func.fn_blocks)` by
    fs[EVERY_MEM] >>
  qexistsl_tac [`before`, `old`, `entry`, `after`] >> simp[] >>
  irule fn_has_code_new_block_segment >> simp[] >>
  qexistsl_tac [`before`, `label`, `old`] >>
  `func.fn_blocks = EL i segments` by
    metis_tac[markerTheory.Abbrev_def, mk_internal_function_metadata] >>
  simp[]
QED

Theorem contract_inv_linked_unit[local]:
  contract_inv mods exps ctx cenv cx ==>
  ?rp unit.
    (if cx.in_deploy then
       ?rbc. lower_vyper_deploy_unit_mods mods exps rp rbc = SOME unit
     else lower_vyper_runtime_unit_mods mods exps rp = SOME unit) /\
    ctx = unit.cu_context /\ cenv.ce_target = rp.rpol_target /\
    (cx.in_deploy ==> IS_SOME (FST (SND (SND (SND (classify_functions_unit mods exps)))))) /\
    IS_SOME (ALOOKUP mods NONE) /\
    EVERY (supported_program o SND) mods
Proof
  rw[contract_inv_def] >> metis_tac[]
QED

Theorem unit_internal_fns_member[local]:
  !mods src tops mut nr rr fname args dflts ret ss.
    MEM (src,tops) mods /\
    MEM (FunctionDecl Internal mut nr rr fname args dflts ret ss) tops ==>
    MEM (src,(mut,nr,rr,fname,args,dflts,ret,ss)) (unit_internal_fns mods)
Proof
  Induct >> simp[] >> qx_gen_tac `m` >> PairCases_on `m` >>
  simp[unit_internal_fns_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[MEM_MAP] >>
  qspec_then `m1` mp_tac classify_fold_internal >>
  simp[] >> metis_tac[]
QED

Theorem order_internals_unit_mem[local]:
  MEM (src,f) (order_internals_unit names fs) <=> MEM (src,f) fs
Proof
  rw[order_internals_unit_def, MEM_FLAT, MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem classified_unit_internal_member[local]:
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl Internal mut nr rr fname args dflts ret ss) tops ==>
  MEM (src,subst_consts_fn_mods (consts_env_mods mods) (mut,nr,rr,fname,args,dflts,ret,ss))
    (FST (SND (classify_functions_unit mods exps)))
Proof
  rpt strip_tac >> simp[classify_functions_unit_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[MEM_MAP] >>
  qexists_tac `(src,mut,nr,rr,fname,args,dflts,ret,ss)` >> simp[] >>
  metis_tac[ALOOKUP_MEM, unit_internal_fns_member]
QED

Theorem unit_package_internal_labels[local]:
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors
      (MAP (set_internal_package_target target o
        package_internal_fn_unit mods trans nkeys is_ctor cap) fs))
Proof
  simp_tac std_ss [internal_fn_descriptors_map, EVERY_MAP, combinTheory.o_DEF] >>
  simp[EVERY_MEM] >> qx_gen_tac `source` >> PairCases_on `source` >> strip_tac >>
  simp[package_internal_fn_unit_def, set_internal_package_target_def,
       internal_label_ok_def, internal_fn_label_def]
QED

Theorem package_internal_labels[local]:
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors
      (MAP (set_internal_package_target target o
        package_internal_fn tops trans nkeys is_ctor cap) fs))
Proof
  simp_tac std_ss [internal_fn_descriptors_map, EVERY_MAP, combinTheory.o_DEF] >>
  simp[EVERY_MEM] >> qx_gen_tac `source` >> PairCases_on `source` >> strip_tac >>
  simp[package_internal_fn_def, set_internal_package_target_def,
       internal_label_ok_def, internal_fn_label_def]
QED

Theorem runtime_internal_run_labels[local]:
  run_lowering sels exts ips fb rp buckets metadata dense info "__entry" = SOME unit /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY (\p. isPREFIX "fn_" (FST p)) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) ==>
  ?start final data.
    compile_generate_runtime sels exts [] fb Linear buckets metadata dense info
      (initial_compile_state "__entry") = ((),start) /\
    compile_internal_fn_bodies ips start = ((),final) /\
    extract_context_with_internals "__entry" ips final = SOME (unit.cu_context,data) /\
    lowering_context_ok unit.cu_context /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)
Proof
  strip_tac >>
  drule_all run_lowering_entry_function_labels >> strip_tac >>
  rename1 `_ (initial_compile_state "__entry") = ((),start)` >>
  qpat_assum `_ (initial_compile_state "__entry") = ((),start)`
    (fn th => qabbrev_tac `prefix = ^(rator (lhs (concl th)))`) >>
  `EVERY (\(sel,lbl). jump_label_ok lbl)
    (MAP (\(sel,lbl,z). (sel,lbl)) sels)` by
    (fs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD, jump_label_ok_def] >>
     metis_tac[]) >>
  `EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)` by
    (qpat_assum `prefix _ = _` mp_tac >> simp_tac std_ss [Abbr `prefix`] >>
     disch_tac >> drule_all runtime_entry_dispatch_code_labels >>
     disch_then strip_assume_tac >> fs[EVERY_MAP]) >>
  `compile_generate_runtime sels exts [] fb Linear buckets metadata dense info
      (initial_compile_state "__entry") = ((),start)` by
    (`comp_bind (comp_return ()) (\_. comp_return ()) = comp_return ()` by
        simp[FUN_EQ_THM, comp_bind_def, comp_return_def] >>
     `compile_generate_runtime sels exts [] fb Linear buckets metadata dense info =
        comp_ignore_bind prefix (comp_return ())` by
        simp[compile_generate_runtime_def, Abbr `prefix`, compile_internal_fn_bodies_def,
             comp_ignore_bind_def, comp_bind_assoc] >>
     simp[comp_ignore_bind_def, comp_bind_def, comp_return_def]) >>
  `rp.rpol_frontend_dispatch = Linear` by
    fs[run_lowering_def, lowering_policy_ok_def, AllCaseEqs()] >>
  Cases_on `compile_internal_fn_bodies ips start` >>
  rename1 `compile_internal_fn_bodies ips start = (u,final)` >> Cases_on `u` >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[run_lowering_def] >>
  once_rewrite_tac[compile_runtime_internal_suffix] >>
  simp[AllCaseEqs()] >> strip_tac >>
  qexistsl_tac [`start`, `final`, `data`] >> gvs[compile_internal_fn_bodies_def, comp_return_def]
QED

Theorem deploy_internal_run_labels[local]:
  run_deploy_lowering T rp bc cap args data_size ips ce ss pay nr key trans
    "__deploy" = SOME unit ==>
  ?start final raw data.
    compile_generate_deploy T (LENGTH bc) cap args data_size [] ce ss pay nr key trans
      (initial_compile_state "__deploy") = ((),start) /\
    compile_internal_fn_bodies ips start = ((),final) /\
    extract_context_with_internals "__deploy" ips final = SOME (raw,data) /\
    unit.cu_context = install_immutable_reservation cap raw /\
    lowering_context_ok unit.cu_context /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)
Proof
  strip_tac >>
  qabbrev_tac `start = SND (compile_generate_deploy T (LENGTH bc) cap args data_size
    [] ce ss pay nr key trans (initial_compile_state "__deploy"))` >>
  `EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)` by
    (qspecl_then [`LENGTH bc`, `cap`, `args`, `data_size`, `ce`, `ss`, `pay`,
        `nr`, `key`, `trans`, `initial_compile_state "__deploy"`]
       mp_tac compile_deploy_entry_labels >>
     qpat_assum `Abbrev (start = _)`
       (fn th => simp[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     strip_tac >> drule cs_extends_block_stream_labels >> strip_tac >>
     qpat_x_assum `MAP _ _ = added_labels _ _` (assume_tac o SYM) >>
     gvs[initial_compile_state_def, EVERY_MEM, internal_label_ok_def] >>
     qx_gen_tac `candidate` >> rpt strip_tac >> gvs[] >>
     `MEM candidate.bb_label (MAP (\b. b.bb_label) tail)` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     res_tac >> Cases_on `candidate.bb_label` >> gvs[]) >>
  Cases_on `compile_internal_fn_bodies ips start` >>
  rename1 `compile_internal_fn_bodies ips start = (u,final)` >> Cases_on `u` >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[run_deploy_lowering_def] >>
  once_rewrite_tac[compile_deploy_internal_suffix] >>
  qpat_assum `Abbrev (start = _)`
    (fn th => simp[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th), AllCaseEqs()]) >>
  strip_tac >>
  qexists_tac `start` >> gvs[] >>
  simp[Abbr `start`] >>
  Cases_on `compile_generate_deploy T (LENGTH bc) cap args data_size
    [] ce ss pay nr key trans (initial_compile_state "__deploy")` >>
  simp[compile_internal_fn_bodies_def, comp_return_def]
QED

Theorem shadow_body_inv_from_internal_runs[local]:
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
  gas_shadow_state start startS /\
  EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start) /\
  EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks startS) ==>
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
  qabbrev_tac `src = subst_consts_fn (module_consts_env tops [])
    (mut,nr,rr,fname,args,dflts,ret,ss)` >>
  `MEM src srcs` by
    (qpat_assum `PERM srcs _` (mp_tac o MATCH_MP PERM_MEM_EQ) >>
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
    (simp[MEM_MAP] >> qexists_tac `src` >>
     simp[Abbr `pkg`]) >>
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
    (REWRITE_RULE [GSYM APPEND_ASSOC, APPEND] selected_internal_shadow_code)) >>
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

Theorem runtime_shadow_body_inv:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
  supported_program tops /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  lower_vyper_runtime_unit tops rp = SOME unit /\
  runtime_gas_shadow_unit tops rp = SOME shadow_unit ==>
  shadow_body_inv tops unit.cu_context shadow_unit.cu_context
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = packages` >> PairCases_on `packages` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor_src)` >>
  `~EXISTS external_has_defaults exts` by fs[] >>
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

(* Grouped defaults compile to the same kind of internal suffix. Pair the
   actual grouped runs, including the code for omitted arguments. *)
Theorem runtime_grouped_shadow_body_inv:
  EXISTS external_has_defaults (FST (classify_functions tops)) /\
  lower_vyper_runtime_unit tops rp = SOME unit ==>
  ?shadow_unit. gas_shadow_unit unit shadow_unit /\
    shadow_body_inv tops unit.cu_context shadow_unit.cu_context
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >>
  rename1 `classify_functions tops = packages` >> PairCases_on `packages` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor_src)` >>
  `EXISTS external_has_defaults exts` by fs[] >>
  qpat_assum `lower_vyper_runtime_unit _ _ = _`
    (mp_tac o REWRITE_RULE [lower_vyper_runtime_unit_def]) >>
  simp[AllCaseEqs()] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_grouped_lowering groups ips fall rp "__entry"` >>
  `EVERY group_entry_labels_ok groups` by
    simp[Abbr `groups`, EVERY_MAP, package_external_group_labels] >>
  qspecl_then [`groups`, `ips`, `fall`, `rp`, `"__entry"`] mp_tac
    gas_shadow_run_grouped_lowering >>
  simp[optionTheory.OPTREL_def] >>
  qmatch_goalsub_abbrev_tac
    `run_grouped_lowering shadow_groups (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fall) rp "__entry"` >>
  Cases_on `run_grouped_lowering shadow_groups (MAP gas_shadow_internal_package ips)
    (OPTION_MAP gas_shadow_fallback_package fall) rp "__entry"` >>
  simp[] >> strip_tac >>
  rename1 `gas_shadow_unit unit shadow_unit` >>
  `EVERY group_entry_labels_ok shadow_groups` by
    (fs[Abbr `shadow_groups`, EVERY_MAP, EVERY_MEM] >>
     rpt strip_tac >> res_tac >> Cases_on `group` >> gvs[group_entry_labels_ok_def] >>
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
    (qspecl_then [`groups`, `[]`, `fall`] mp_tac
       gas_shadow_compile_generate_grouped_runtime >>
     qpat_assum `Abbrev (shadow_groups = _)` (fn th =>
       simp[gas_shadow_compiles_def, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     disch_then (qspecl_then [`initial_compile_state "__entry"`,
       `initial_compile_state "__entry"`] mp_tac) >>
     simp[gas_shadow_state_refl]) >>
  rename1 `extract_context_with_internals "__entry" _ run_endS =
    SOME (shadow_unit.cu_context,shadow_data)` >>
  qexists_tac `shadow_unit` >> simp[] >>
  mp_tac (Q.INST [`is_ctor` |-> `F`, `name` |-> `"__entry"`, `raw` |-> `unit.cu_context`,
    `rawS` |-> `shadow_unit.cu_context`, `dataS` |-> `shadow_data`,
    `srcs` |-> `order_internals (runtime_internal_order tops ints) ints`]
    shadow_body_inv_from_internal_runs) >>
  fs[Abbr `ips`, PERM_order_runtime_internals, gas_shadow_unit_def]
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

Theorem selected_unit_internal_run[local]:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  MEM (FunctionDecl Internal mut nr rr fname args dflts ret ss) tops ==>
  ?ips start final name raw data.
    MEM (set_internal_package_target cenv.ce_target
      (package_internal_fn_unit mods T (K global_nonreentrant_slot) cx.in_deploy
        (if cx.in_deploy then imm_len_mods mods else 0)
        (src,subst_consts_fn_mods (consts_env_mods mods)
          (mut,nr,rr,fname,args,dflts,ret,ss)))) ips /\
    compile_internal_fn_bodies ips start = ((),final) /\
    extract_context_with_internals name ips final = SOME (raw,data) /\
    raw.ctx_functions = ctx.ctx_functions /\
    lowering_context_ok ctx /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)
Proof
  strip_tac >> drule contract_inv_linked_unit >> strip_tac >>
  `ALOOKUP mods src = SOME tops` by metis_tac[module_body_inv_lookup] >>
  `MEM (src,subst_consts_fn_mods (consts_env_mods mods)
     (mut,nr,rr,fname,args,dflts,ret,ss))
     (FST (SND (classify_functions_unit mods exps)))` by
    metis_tac[classified_unit_internal_member] >>
  Cases_on `classify_functions_unit mods exps` >>
  rename1 `classify_functions_unit mods exps = classified` >>
  PairCases_on `classified` >>
  rename1 `classify_functions_unit mods exps = (exts,ints,fb,cf,ctors)` >>
  fs[] >>
  Cases_on `cx.in_deploy` >> fs[]
  >- (Cases_on `cf` >> gvs[] >>
      rename1 `classify_functions_unit _ _ = (_,_,_,SOME constructor,_)` >>
      Cases_on `set_constructor_package_target rp.rpol_target
         (package_constructor_unit mods T (K global_nonreentrant_slot) constructor)` >>
      rename1 `set_constructor_package_target _ _ = cpkg` >>
      PairCases_on `cpkg` >>
      qabbrev_tac `srcs = order_internals_unit
        (deploy_internal_order_unit (SOME constructor) (ints ++ ctors)) (ints ++ ctors)` >>
      qabbrev_tac `ips = MAP (set_internal_package_target rp.rpol_target o
        package_internal_fn_unit mods T (K global_nonreentrant_slot) T
          (imm_len_mods mods)) srcs` >>
      `run_deploy_lowering T rp rbc (imm_len_mods mods) cpkg1 0 ips
        cpkg0 cpkg6 cpkg2 cpkg3 cpkg4 cpkg5 "__deploy" = SOME unit` by
        (qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
         simp[lower_vyper_deploy_unit_mods_def, GSYM imm_len_mods_def,
              Abbr `ips`, Abbr `srcs`, AllCaseEqs()]) >>
      drule deploy_internal_run_labels >> strip_tac >>
      `raw.ctx_functions = unit.cu_context.ctx_functions` by
        fs[install_immutable_reservation_def] >>
      qexistsl_tac [`ips`, `start`, `final`, `"__deploy"`, `raw`, `data`] >>
      simp[Abbr `ips`, unit_package_internal_labels, MEM_MAP] >>
      qexists_tac `(src,subst_consts_fn_mods (consts_env_mods mods)
        (mut,nr,rr,fname,args,dflts,ret,ss))` >>
      simp[Abbr `srcs`, order_internals_unit_mem, MEM_APPEND]) >>
  qabbrev_tac `srcs = order_internals_unit
    (runtime_internal_order_unit (exported_runtime_fns mods exps)
      (main_module mods) ints) ints` >>
  qabbrev_tac `ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) F 0) srcs` >>
  `MEM (set_internal_package_target rp.rpol_target
        (package_internal_fn_unit mods T (K global_nonreentrant_slot) F 0
          (src,subst_consts_fn_mods (consts_env_mods mods)
            (mut,nr,rr,fname,args,dflts,ret,ss)))) ips` by
    (simp[Abbr `ips`, MEM_MAP] >>
     qexists_tac `(src,subst_consts_fn_mods (consts_env_mods mods)
       (mut,nr,rr,fname,args,dflts,ret,ss))` >>
     simp[Abbr `srcs`, order_internals_unit_mem]) >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    simp[Abbr `ips`, unit_package_internal_labels] >>
  Cases_on `EXISTS (external_has_defaults o SND) exts`
  >- (qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
      simp[lower_vyper_runtime_unit_mods_def, Abbr `ips`, Abbr `srcs`,
           AllCaseEqs()] >> strip_tac >>
      drule grouped_internal_run_labels >>
      simp[EVERY_MAP, package_external_group_unit_labels] >> strip_tac >>
      qpat_assum `compile_internal_fn_bodies _ start = ((),final)`
        (fn th => qexists_tac `^(rand (rator (lhs (concl th))))`) >>
      qexistsl_tac [`start`, `final`, `"__entry"`, `unit.cu_context`, `data`] >>
      simp[]) >>
  qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_mods_def, Abbr `ips`, Abbr `srcs`,
       AllCaseEqs()] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_lowering sels packs runtime_ips fall rp 0 0 [] info "__entry"` >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels` by
    simp[Abbr `sels`, build_selectors_fn_labels] >>
  `EVERY (\p. isPREFIX "fn_" (FST p)) packs` by
    simp[Abbr `packs`, EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
         package_external_fn_unit_def, set_external_package_target_def] >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors runtime_ips)` by
    simp[Abbr `runtime_ips`, unit_package_internal_labels] >>
  drule_all runtime_internal_run_labels >> strip_tac >>
  qexistsl_tac [`runtime_ips`, `start`, `final`, `"__entry"`, `unit.cu_context`, `data`] >>
  simp[]
QED

Theorem body_inv_selected_internal_code_mods:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  MEM (FunctionDecl Internal mut nr rr fname args dflts ret ss) tops /\
  lookup_function
    (internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,fname)))
      (nsid_to_string (src,fname)) (MAP SND args) cx.in_deploy)
    ctx.ctx_functions = SOME callee ==>
  ?label ce params has_rb nr' key trans view ctor ilen rt before old entry final.
    set_internal_package_target cenv.ce_target
      (package_internal_fn_unit mods T (K global_nonreentrant_slot) cx.in_deploy
        (if cx.in_deploy then imm_len_mods mods else 0)
        (src,subst_consts_fn_mods (consts_env_mods mods)
          (mut,nr,rr,fname,args,dflts,ret,ss))) =
      (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,
        subst_consts_stmts_mods (consts_env_mods mods) ss,rt) /\
    label = internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,fname)))
      (nsid_to_string (src,fname)) (MAP SND args) cx.in_deploy /\
    new_block label before = (old,entry) /\
    compile_internal_function ce params has_rb nr' key trans view ctor ilen
      (subst_consts_stmts_mods (consts_env_mods mods) ss) rt entry = ((),final) /\
    fn_has_code entry final callee /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
    ctx_inst_ids_distinct ctx
Proof
  strip_tac >> drule_all selected_unit_internal_run >> strip_tac >>
  qpat_assum `MEM _ ips` (fn th =>
    qabbrev_tac `pkg = ^(rand (rator (concl th)))`) >>
  PairCases_on `pkg` >>
  qpat_assum `Abbrev (_ = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `pkg0 = internal_fn_label
      (build_func_ids_mods 0 mods (nsid_to_string (src,fname)))
      (nsid_to_string (src,fname)) (MAP SND args) cx.in_deploy /\
    pkg10 = subst_consts_stmts_mods (consts_env_mods mods) ss` by
    (qpat_assum `(_,_,_,_,_,_,_,_,_,_,_,_) = set_internal_package_target _ _` mp_tac >>
     simp_tac std_ss [subst_consts_fn_mods_def, package_internal_fn_unit_def,
       set_internal_package_target_def, LET_THM, pairTheory.PAIR_EQ] >>
     strip_tac >> asm_rewrite_tac[]) >>
  `ALL_DISTINCT (MAP (\f. f.fn_name) raw.ctx_functions) /\
    EVERY (\f. ALL_DISTINCT (MAP (\bb. bb.bb_label) f.fn_blocks)) raw.ctx_functions /\
    ctx_inst_ids_distinct ctx` by
    (fs[lowering_context_ok_def, ctx_fn_names_def, fn_labels_def, EVERY_MEM] >>
     metis_tac[]) >>
  `lookup_function pkg0 raw.ctx_functions = SOME callee` by fs[] >>
  drule_all extract_context_internal_code_by_labels >> strip_tac >>
  qexistsl_tac [`pkg0`, `pkg1`, `pkg2`, `pkg3`, `pkg4`, `pkg5`, `pkg6`,
    `pkg7`, `pkg8`, `pkg9`, `pkg11`, `before`, `old`, `entry`, `after`] >>
  qpat_x_assum `pkg10 = _` SUBST_ALL_TAC >> fs[]
QED

Theorem body_inv_selected_internal_code:
  body_inv tops ctx cenv cx /\
  MEM (FunctionDecl Internal mut nr rr fname args dflts ret ss) tops /\
  lookup_function
    (internal_fn_label (build_func_ids 0 tops fname) fname (MAP SND args)
       cx.in_deploy) ctx.ctx_functions = SOME callee ==>
  ?label ce params has_rb nr' key trans view ctor ilen rt before old entry final.
    set_internal_package_target cenv.ce_target
      (package_internal_fn tops T (K global_nonreentrant_slot) cx.in_deploy
        (if cx.in_deploy then imm_len tops else 0)
        (subst_consts_fn (module_consts_env tops [])
          (mut,nr,rr,fname,args,dflts,ret,ss))) =
      (label,ce,params,has_rb,nr',key,trans,view,ctor,ilen,
        subst_consts_stmts (module_consts_env tops []) ss,rt) /\
    label = internal_fn_label (build_func_ids 0 tops fname) fname
      (MAP SND args) cx.in_deploy /\
    new_block label before = (old,entry) /\
    compile_internal_function ce params has_rb nr' key trans view ctor ilen
      (subst_consts_stmts (module_consts_env tops []) ss) rt entry = ((),final) /\
    fn_has_code entry final callee /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
    ctx_inst_ids_distinct ctx
Proof
  strip_tac >> drule body_inv_contract >> drule body_inv_module >> rpt strip_tac >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`, `exps` |-> `[]`]
    body_inv_selected_internal_code_mods) >>
  simp[package_internal_fn_unit_singleton, build_func_ids_mods_singleton,
       nsid_to_string_def, imm_len_mods_singleton, consts_env_mods_singleton,
       subst_consts_fn_mods_singleton, subst_consts_mods_singleton]
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
    function_mutability_ok_def, stmt_mutability_ok_def, listTheory.APPEND_EQ_SING] >>
  qexistsl_tac [`<| rpol_target := all_capabilities;
                   rpol_frontend_dispatch := Linear;
                   rpol_final_assembly := FAP_Optimize |>`, `unit`] >>
  simp[]
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

Theory bodyFullShadowInternalRun
Ancestors
  bodyFullShadowInternalCode compileVyper vyperCompiler compileEnv moduleLowering
  loweringShapeProps loweringShapeDefs ctorDeployEntryLabels supportedProgram
  venomInst list rich_list bodyInvSplit bodyInvModuleProps
  bodyInternalFunctionIntervalProps internalBlockPackagingProps compileUnit
  constSubstMods groupedInternalLabels intCallLookup alist pair externalEntryShape
  externalEntryChecks context ctorDeployDefs constSubst bodySim[qualified]
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

Theorem packaged_internal_mode:
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

(* A label the extracted context resolves belongs to a packaged source
   function, whose id is the label's. *)
Theorem packaged_internal_source_id:
  ips = MAP (set_internal_package_target target o
    package_internal_fn tops T (K global_nonreentrant_slot) is_ctor cap)
      (srcs : (function_mutability # bool # bool # string #
        (string # type) list # expr list # type # stmt list) list) /\
  name = (if is_ctor then "__deploy" else "__entry") /\
  extract_context_with_internals name ips run_end = SOME (raw,data) /\
  lookup_function (internal_fn_label id fname tys mode) raw.ctx_functions =
    SOME callee ==>
  ?src. MEM src srcs /\ id = build_func_ids 0 tops (FST (SND (SND (SND src))))
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
  simp[] >> strip_tac >>
  drule internal_fn_label_id_11 >> strip_tac >>
  simp[pairTheory.EXISTS_PROD] >> metis_tac[]
QED

Theorem extract_context_internal_code_by_labels:
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
    IS_SOME (ALOOKUP mods NONE)
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

(* The raw pool contributes only Internal declarations and imported Deploy
   declarations. Name provenance is all that ID separation needs. *)
Theorem raw_unit_candidate_origin[local]:
  !mods m f. MEM (m,f) (unit_internal_fns mods ++ imported_ctors mods) ==>
  ?tops v mut nr rr args dflts ret ss.
    MEM (m,tops) mods /\ v <> External /\
    MEM (FunctionDecl v mut nr rr (fn_decl_name f) args dflts ret ss) tops
Proof
  Induct >- simp[unit_internal_fns_def, imported_ctors_def] >>
  qx_gen_tac `md` >> PairCases_on `md` >>
  simp[unit_internal_fns_def, imported_ctors_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[MEM_APPEND, MEM_MAP] >> rpt gen_tac >> strip_tac
  >- (PairCases_on `f` >> gvs[fn_decl_name_def] >>
      qspec_then `md1` mp_tac classify_fold_internal >> simp[] >>
      metis_tac[vyperASTTheory.function_visibility_distinct])
  >- metis_tac[]
  >- (Cases_on `md0` >> Cases_on `ctor` >> gvs[] >>
      PairCases_on `f` >> gvs[] >>
      qspec_then `md1` mp_tac classify_functions_ctor_mem >>
      simp[classify_functions_def, subst_consts_fn_def, fn_decl_name_def] >>
      metis_tac[vyperASTTheory.function_visibility_distinct])
  >> metis_tac[]
QED

Theorem classified_unit_candidate_origin[local]:
  classify_functions_unit mods exps = (exts,ints,fb,cf,ctors) /\
  MEM (m,f) (ints ++ ctors) ==>
  ?tops v mut nr rr args dflts ret ss.
    MEM (m,tops) mods /\ v <> External /\
    MEM (FunctionDecl v mut nr rr (fn_decl_name f) args dflts ret ss) tops
Proof
  simp[classify_functions_unit_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[MEM_MAP, EXISTS_PROD] >>
  rename1 `MEM (m,g) _` >>
  `MEM (m,g) (unit_internal_fns mods ++ imported_ctors mods)` by
    simp[MEM_APPEND] >>
  drule raw_unit_candidate_origin >>
  PairCases_on `g` >>
  simp[fn_decl_name_def, subst_consts_fn_mods_def]
QED

Theorem classified_unit_candidate_ids_11[local]:
  classify_functions_unit mods exps = (exts,ints,fb,cf,ctors) /\
  MEM (s,f) (ints ++ ctors) /\ MEM (m,g) (ints ++ ctors) /\
  build_func_ids_mods n mods (nsid_to_string (s,fn_decl_name f)) =
  build_func_ids_mods n mods (nsid_to_string (m,fn_decl_name g)) ==>
  nsid_to_string (s,fn_decl_name f) = nsid_to_string (m,fn_decl_name g)
Proof
  strip_tac >>
  `?tops v mut nr rr args dflts ret ss.
     MEM (s,tops) mods /\ v <> External /\
     MEM (FunctionDecl v mut nr rr (fn_decl_name f) args dflts ret ss) tops` by
    metis_tac[classified_unit_candidate_origin] >>
  `?tops v mut nr rr args dflts ret ss.
     MEM (m,tops) mods /\ v <> External /\
     MEM (FunctionDecl v mut nr rr (fn_decl_name g) args dflts ret ss) tops` by
    metis_tac[classified_unit_candidate_origin] >>
  irule build_func_ids_mods_11 >> metis_tac[]
QED

Theorem order_internals_unit_mem[local]:
  MEM (src,f) (order_internals_unit names fs) <=>
  MEM (src,f) fs /\ MEM (nsid_to_string (src,fn_decl_name f)) names
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

Theorem package_internal_labels:
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

Theorem runtime_internal_run_labels:
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

Theorem deploy_internal_run_labels:
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

Theorem runtime_unit_ordered_run[local]:
  lower_vyper_runtime_unit_mods mods exps rp = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,cf,ctors) /\
  ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) F 0)
    (order_internals_unit (runtime_internal_order_unit
      (exported_runtime_fns mods exps) (main_module mods) ints) ints) ==>
  ?start final data.
    compile_internal_fn_bodies ips start = ((),final) /\
    extract_context_with_internals "__entry" ips final = SOME (unit.cu_context,data) /\
    lowering_context_ok unit.cu_context /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)
Proof
  strip_tac >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    simp[unit_package_internal_labels] >>
  qpat_x_assum `ips = MAP _ _` (assume_tac o SYM) >>
  Cases_on `EXISTS (external_has_defaults o SND) exts`
  >- (qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
      simp[lower_vyper_runtime_unit_mods_def, AllCaseEqs()] >> strip_tac >>
      drule grouped_internal_run_labels >>
      simp[EVERY_MAP, package_external_group_unit_labels] >> strip_tac >>
      qexistsl_tac [`start`, `final`, `data`] >> simp[]) >>
  qpat_x_assum `lower_vyper_runtime_unit_mods _ _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_mods_def, AllCaseEqs()] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_lowering sels packs ips fall rp 0 0 [] info "__entry"` >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels` by
    simp[Abbr `sels`, build_selectors_fn_labels] >>
  `EVERY (\p. isPREFIX "fn_" (FST p)) packs` by
    simp[Abbr `packs`, EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
         package_external_fn_unit_def, set_external_package_target_def] >>
  drule_all runtime_internal_run_labels >> strip_tac >>
  qexistsl_tac [`start`, `final`, `data`] >> simp[]
QED

Theorem unit_ordered_lookup_member[local]:
  key = nsid_to_string (s,fn_decl_name f) /\
  MEM (s,f) pool /\
  ips = MAP (set_internal_package_target tgt o
    package_internal_fn_unit mods trans keys ctor cap)
    (order_internals_unit names pool) /\
  extract_context_with_internals entry ips final = SOME (raw,data) /\
  lookup_function (internal_fn_label (build_func_ids_mods 0 mods key)
    printed tys mode) raw.ctx_functions = SOME callee /\
  internal_fn_label (build_func_ids_mods 0 mods key) printed tys mode <> entry /\
  (!m g. MEM (m,g) pool /\
     build_func_ids_mods 0 mods key =
       build_func_ids_mods 0 mods (nsid_to_string (m,fn_decl_name g)) ==>
     key = nsid_to_string (m,fn_decl_name g)) ==>
  MEM (s,f) (order_internals_unit names pool)
Proof
  strip_tac >>
  `MEM (internal_fn_label (build_func_ids_mods 0 mods key) printed tys mode)
    (entry :: MAP FST (internal_fn_descriptors ips))` by
    metis_tac[venomInstTheory.lookup_function_mem, extract_context_internal_names] >>
  qpat_x_assum `ips = _` SUBST_ALL_TAC >>
  qpat_x_assum `MEM _ (_ :: _)` mp_tac >>
  pure_rewrite_tac[internal_fn_descriptors_map, listTheory.MAP_MAP_o] >>
  simp[MEM_MAP, combinTheory.o_DEF] >>
  disch_then (qx_choose_then `w` strip_assume_tac) >>
  Cases_on `w` >>
  qmatch_asmsub_rename_tac `MEM (owner,decl) (order_internals_unit _ _)` >>
  qpat_x_assum `!m g. _` (qspecl_then [`owner`, `decl`] assume_tac) >>
  PairCases_on `decl` >>
  qpat_x_assum `internal_fn_label _ _ _ _ = _` mp_tac >>
  simp[package_internal_fn_unit_def, set_internal_package_target_def] >>
  strip_tac >> drule internal_fn_label_id_11 >> strip_tac >>
  qpat_x_assum `key = _` SUBST_ALL_TAC >>
  fs[order_internals_unit_mem, fn_decl_name_def] >> metis_tac[]
QED

Theorem deploy_unit_ordered_run[local]:
  lower_vyper_deploy_unit_mods mods exps rp bc = SOME unit /\
  classify_functions_unit mods exps = (exts,ints,fb,SOME constructor,ctors) /\
  ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) T
      (imm_len_mods mods))
    (order_internals_unit (deploy_internal_order_unit (SOME constructor)
      (ints ++ ctors)) (ints ++ ctors)) ==>
  ?start final raw data.
    compile_internal_fn_bodies ips start = ((),final) /\
    extract_context_with_internals "__deploy" ips final = SOME (raw,data) /\
    raw.ctx_functions = unit.cu_context.ctx_functions /\
    lowering_context_ok unit.cu_context /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)
Proof
  strip_tac >>
  Cases_on `set_constructor_package_target rp.rpol_target
    (package_constructor_unit mods T (K global_nonreentrant_slot) constructor)` >>
  rename1 `set_constructor_package_target _ _ = cpkg` >>
  PairCases_on `cpkg` >>
  `run_deploy_lowering T rp bc (imm_len_mods mods) cpkg1 0 ips
    cpkg0 cpkg6 cpkg2 cpkg3 cpkg4 cpkg5 "__deploy" = SOME unit` by
    (qpat_x_assum `lower_vyper_deploy_unit_mods _ _ _ _ = _` mp_tac >>
     simp[lower_vyper_deploy_unit_mods_def, GSYM imm_len_mods_def, AllCaseEqs()]) >>
  drule deploy_internal_run_labels >> strip_tac >>
  `raw.ctx_functions = unit.cu_context.ctx_functions` by
    fs[install_immutable_reservation_def] >>
  qexistsl_tac [`start`, `final`, `raw`, `data`] >>
  simp[unit_package_internal_labels]
QED

(* The lowering packages only the reachable internal functions.  The lookup
   premise says this one's label resolves in the unit, so some packaged
   function has the same id (internal_fn_label_id_11), hence the same key
   (build_func_ids_mods_11); that key is reachable, and the function itself
   is classified (classified_unit_internal_member), so it is packaged too. *)
Theorem selected_unit_internal_run:
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  MEM (FunctionDecl Internal mut nr rr fname args dflts ret ss) tops /\
  lookup_function
    (internal_fn_label (build_func_ids_mods 0 mods (nsid_to_string (src,fname)))
      (nsid_to_string (src,fname)) (MAP SND args) cx.in_deploy)
    ctx.ctx_functions = SOME callee ==>
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
  qabbrev_tac `f = subst_consts_fn_mods (consts_env_mods mods)
    (mut,nr,rr,fname,args,dflts,ret,ss)` >>
  `ALOOKUP mods src = SOME tops` by metis_tac[module_body_inv_lookup] >>
  `MEM (src,f) (FST (SND (classify_functions_unit mods exps)))` by
    metis_tac[classified_unit_internal_member, markerTheory.Abbrev_def] >>
  Cases_on `classify_functions_unit mods exps` >>
  rename1 `classify_functions_unit mods exps = classified` >>
  PairCases_on `classified` >>
  rename1 `classify_functions_unit mods exps = (exts,ints,fb,cf,ctors)` >> fs[] >>
  qabbrev_tac `pool = if cx.in_deploy then ints ++ ctors else ints` >>
  qabbrev_tac `names = if cx.in_deploy then deploy_internal_order_unit cf pool
    else runtime_internal_order_unit (exported_runtime_fns mods exps)
      (main_module mods) pool` >>
  qabbrev_tac `entry = if cx.in_deploy then "__deploy" else "__entry"` >>
  qabbrev_tac `ips = MAP (set_internal_package_target rp.rpol_target o
    package_internal_fn_unit mods T (K global_nonreentrant_slot) cx.in_deploy
      (if cx.in_deploy then imm_len_mods mods else 0)) (order_internals_unit names pool)` >>
  `?start final raw data.
    compile_internal_fn_bodies ips start = ((),final) /\
    extract_context_with_internals entry ips final = SOME (raw,data) /\
    raw.ctx_functions = unit.cu_context.ctx_functions /\
    lowering_context_ok unit.cu_context /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
    EVERY (\bb. ~internal_label_ok bb.bb_label) (all_blocks start)` by
    (Cases_on `cx.in_deploy` >> fs[Abbr `entry`, Abbr `names`, Abbr `pool`]
     >- (Cases_on `cf` >- fs[] >>
         qpat_x_assum `Abbrev (ips = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
         drule_all deploy_unit_ordered_run >> disch_then ACCEPT_TAC) >>
     qpat_x_assum `Abbrev (ips = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all runtime_unit_ordered_run >> strip_tac >>
     qexistsl_tac [`start`, `final`, `unit.cu_context`, `data`] >> simp[]) >>
  qabbrev_tac `key = nsid_to_string (src,fname)` >>
  `key = nsid_to_string (src,fn_decl_name f)` by
    simp[Abbr `key`, Abbr `f`, subst_consts_fn_mods_def, fn_decl_name_def] >>
  `MEM (src,f) pool` by (Cases_on `cx.in_deploy` >> simp[Abbr `pool`, MEM_APPEND]) >>
  `!m g. MEM (m,g) pool /\ build_func_ids_mods 0 mods key =
       build_func_ids_mods 0 mods (nsid_to_string (m,fn_decl_name g)) ==>
     key = nsid_to_string (m,fn_decl_name g)` by
    (rpt strip_tac >> simp[] >> irule classified_unit_candidate_ids_11 >>
     Cases_on `cx.in_deploy` >> fs[Abbr `pool`, MEM_APPEND] >> metis_tac[]) >>
  `internal_fn_label (build_func_ids_mods 0 mods key) key (MAP SND args) cx.in_deploy <> entry` by
    (Cases_on `cx.in_deploy` >> simp[Abbr `entry`, internal_fn_label_def]) >>
  `lookup_function (internal_fn_label (build_func_ids_mods 0 mods key) key
     (MAP SND args) cx.in_deploy) raw.ctx_functions = SOME callee` by
    (qpat_assum `raw.ctx_functions = _` (fn th => pure_rewrite_tac[th]) >>
     first_assum ACCEPT_TAC) >>
  `MEM (src,f) (order_internals_unit names pool)` by
    (qpat_x_assum `Abbrev (ips = _)` (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     drule_all unit_ordered_lookup_member >> disch_then ACCEPT_TAC) >>
  qexistsl_tac [`ips`, `start`, `final`, `entry`, `raw`, `data`] >> simp[] >>
  simp[Abbr `ips`, MEM_MAP] >> qexists_tac `(src,f)` >> simp[]
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
  strip_tac >> drule bodySimTheory.body_inv_contract >>
  drule bodySimTheory.body_inv_module >> rpt strip_tac >>
  mp_tac (Q.INST [`mods` |-> `[(NONE,tops)]`, `src` |-> `NONE`, `exps` |-> `[]`]
    body_inv_selected_internal_code_mods) >>
  simp[package_internal_fn_unit_singleton, build_func_ids_mods_singleton,
       nsid_to_string_def, imm_len_mods_singleton, consts_env_mods_singleton,
       subst_consts_fn_mods_singleton, subst_consts_mods_singleton]
QED

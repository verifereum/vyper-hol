Theory entryRejectCode
Ancestors
  entryCodeOwnership entryRawFunction moduleLowering compileEnv list pair
  loweringShapeProps loweringShapeDefs loweringShapeRules vyperCompiler venomInst
  entryBodyBoundLabels entryCompileIntervals entryInternalAppend entryLinearAppend
  entryPrefixRetention fragExec venomExecProofs emitHelperProps
  allocaFrontierBound venomWf removeUnusedSsaProofs venomWfProps
  groupedInternalLabels compileVyper

Theorem compile_runtime_entry_intervals[local]:
  compile_generate_runtime sels exts ints fb Linear buckets meta dense info sa =
    ((),sz) ==>
  ?fl sf sd sx sn se.
    fresh_label "fallback" sa = (fl,sf) /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,_). (sel,lbl)) sels) fl sf = ((),sd) /\
    compile_external_fn_bodies exts sd = ((),sx) /\
    new_block fl sx = (sx.cs_current_bb,sn) /\
    (case fb of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
         compile_fallback_body ce pay nr key tr view stmts rt) sn = ((),se) /\
    compile_internal_fn_bodies ints se = ((),sz)
Proof
  simp[compile_generate_runtime_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> gvs[new_block_def]
QED

Theorem compile_runtime_without_internals_prefix[local]:
  compile_generate_runtime sels exts ints fb Linear buckets meta dense info sa =
    ((),sz) ==>
  ?se.
    compile_generate_runtime sels exts [] fb Linear buckets meta dense info sa =
      ((),se) /\
    compile_internal_fn_bodies ints se = ((),sz)
Proof
  strip_tac >> drule compile_runtime_entry_intervals >> strip_tac >>
  qexists_tac `se` >> simp[] >>
  simp[compile_generate_runtime_def, comp_ignore_bind_def, comp_bind_def,
       comp_return_def, compile_internal_fn_bodies_def]
QED

Theorem runtime_entry_label_class[local]:
  compile_generate_runtime sels exts [] fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),se) /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl) exts ==>
  EVERY (\l. l = "__entry" \/ jump_label_ok l)
    (MAP (\bb. bb.bb_label) (all_blocks se))
Proof
  strip_tac >>
  `EVERY (\l. l = "__entry" \/ jump_label_ok l)
    (MAP (\bb. bb.bb_label) (all_blocks (SND
      (compile_generate_runtime sels exts [] fb Linear bc mb db ei
        (initial_compile_state "__entry")))))` suffices_by simp[] >>
  irule bound_labels_runtime_linear_no_internals >>
  conj_tac >- simp[jump_label_ok_def] >>
  simp[initial_compile_state_def, all_blocks_def] >>
  gvs[EVERY_MEM, FORALL_PROD] >> metis_tac[]
QED

Theorem runtime_entry_delimiter_exclusion[local]:
  compile_generate_runtime sels exts [] fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),se) /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) ds ==>
  !d. MEM d ds ==> ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks se))
Proof
  strip_tac >> drule_all runtime_entry_label_class >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `internal_label_ok (FST d)` by gvs[EVERY_MEM] >>
  `FST d <> "__entry"` by (strip_tac >> gvs[internal_label_ok_def]) >>
  metis_tac[jump_label_ok_names]
QED

Theorem internal_fn_bodies_all_blocks_prefix[local]:
  compile_internal_fn_bodies ints se = ((),sz) ==>
  ?tail. all_blocks sz = all_blocks se ++ tail
Proof
  Cases_on `ints = []`
  >- simp[compile_internal_fn_bodies_def, comp_return_def] >>
  metis_tac[internal_fn_bodies_retains_prefix]
QED

Theorem runtime_packaged_entry_retains[local]:
  compile_generate_runtime sels exts ints fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),sz) /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  package_internal_blocks (internal_fn_descriptors ints) (all_blocks sz) =
    SOME (eb,fs) ==>
  ?se rest. compile_generate_runtime sels exts [] fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),se) /\
    eb = all_blocks se ++ rest
Proof
  strip_tac >> drule compile_runtime_without_internals_prefix >> strip_tac >>
  `!d. MEM d (internal_fn_descriptors ints) ==>
    ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks se))` by
    (metis_tac[runtime_entry_delimiter_exclusion]) >>
  drule internal_fn_bodies_all_blocks_prefix >> strip_tac >>
  qexists_tac `se` >> simp[] >>
  irule package_internal_blocks_prefix >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem run_lowering_retained_entry_distinct:
  run_lowering sels exts ints fb rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn ==>
  ?se. compile_generate_runtime sels exts [] fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),se) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se)) /\
    (!bb. MEM bb (all_blocks se) ==>
      lookup_block bb.bb_label efn.fn_blocks = SOME bb)
Proof
  strip_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def] >> strip_tac >> pairarg_tac >>
  gvs[AllCaseEqs(), lowering_policy_ok_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) efn.fn_blocks)` by
    (drule lowering_context_ok_bridge >> strip_tac >>
     `MEM efn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
     gvs[EVERY_MEM, fn_labels_def] >> metis_tac[]) >>
  qpat_assum `extract_context_with_internals _ _ _ = _`
    (mp_tac o REWRITE_RULE [extract_context_with_internals_def]) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  fs[GSYM all_blocks_def] >>
  drule_all runtime_packaged_entry_retains >> strip_tac >>
  `efn.fn_blocks = entry_blocks` by (drule_all extracted_entry_blocks >> simp[]) >>
  qexists_tac `se` >> simp[] >> conj_tac
  >- gvs[MAP_APPEND, ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> irule MEM_lookup_block >> gvs[MEM_APPEND]
QED

Theorem run_lowering_retained_entry:
  run_lowering sels exts ints fb rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn ==>
  ?se. compile_generate_runtime sels exts [] fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),se) /\
    (!bb. MEM bb (all_blocks se) ==>
      lookup_block bb.bb_label efn.fn_blocks = SOME bb)
Proof
  strip_tac >> drule_all run_lowering_retained_entry_distinct >> metis_tac[]
QED

Theorem run_grouped_lowering_retained_entry_prefix:
  run_grouped_lowering groups ips fb rp "__entry" = SOME u /\
  EVERY group_entry_labels_ok groups /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn ==>
  ?se rest. compile_generate_grouped_runtime groups [] fb
    (initial_compile_state "__entry") = ((),se) /\
    efn.fn_blocks = all_blocks se ++ rest
Proof
  strip_tac >> drule_all grouped_internal_run_labels >> strip_tac >>
  qpat_assum `extract_context_with_internals _ _ _ = _`
    (mp_tac o REWRITE_RULE [extract_context_with_internals_def]) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  fs[GSYM all_blocks_def] >>
  `!d. MEM d (internal_fn_descriptors ips) ==>
    ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks start))` by
    (simp[MEM_MAP] >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule internal_fn_bodies_all_blocks_prefix >> strip_tac >>
  `efn.fn_blocks = entry_blocks` by (drule_all extracted_entry_blocks >> simp[]) >>
  simp[] >> metis_tac[package_internal_blocks_prefix]
QED

Theorem run_grouped_lowering_dispatch_code:
  run_grouped_lowering groups ips fb rp "__entry" = SOME unit /\
  EVERY group_entry_labels_ok groups /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips) /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn ==>
  ?sf fallback jobs sd sx sn se.
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback,sf) /\
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    sf.cs_next_var = 0 /\ sf.cs_next_id = 0 /\
    compile_group_dispatch_linear groups fallback sf = (jobs,sd) /\
    fn_has_code sf sd fn /\ fn_has_code sd sx fn /\
    compile_external_jobs jobs sd = ((),sx) /\
    new_block fallback sx = (sx.cs_current_bb,sn) /\
    sn.cs_current_bb = fallback /\ sn.cs_current_insts = [] /\
    (case fb of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
         compile_fallback_body ce pay nr key tr view stmts rt) sn = ((),se) /\
    fn_has_code sn se fn /\
    EVERY group_job_label_ok jobs /\
    cs_extends sf sd /\ cs_extends sd se /\ cs_extends sx se /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se)) /\
    (!bb. MEM bb (all_blocks se) ==>
       lookup_block bb.bb_label fn.fn_blocks = SOME bb)
Proof
  strip_tac >> drule_all run_grouped_lowering_retained_entry_prefix >>
  disch_then (qx_choosel_then [`se`,`rest`] strip_assume_tac) >>
  drule run_grouped_lowering_context >>
  disch_then (strip_assume_tac o MATCH_MP lowering_context_ok_bridge) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (`MEM fn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
     gvs[EVERY_MEM, fn_labels_def] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se))` by
    gvs[MAP_APPEND, ALL_DISTINCT_APPEND] >>
  `!bb. MEM bb (all_blocks se) ==> lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (rpt strip_tac >> irule MEM_lookup_block >> fs[MEM_APPEND]) >>
  drule_all compile_grouped_runtime_entry_layout >>
  disch_then (qx_choosel_then [`fl`,`sf`,`jobs`,`sd`,`sx`,`sn`] strip_assume_tac) >>
  `cs_extends sd se` by metis_tac[cs_extends_trans] >>
  `fn_has_code sf sd fn /\ fn_has_code sd sx fn` by
    metis_tac[fn_has_code_retained_interval] >>
  `fn_has_code sn se fn` by metis_tac[fn_has_code_endpoint_coverage] >>
  `sn.cs_current_bb = fl /\ sn.cs_current_insts = []` by metis_tac[new_block_props] >>
  qexistsl_tac [`sf`,`fl`,`jobs`,`sd`,`sx`,`sn`,`se`] >>
  asm_rewrite_tac[] >>
  qpat_x_assum `fresh_label _ _ = _` mp_tac >>
  simp[fresh_label_def, initial_compile_state_def]
QED

Theorem run_lowering_fallback_revert_code:
  run_lowering sels exts ints NONE rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,ss,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn ==>
  ?fl sf sd checks se.
    fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fl sf = ((),sd) /\
    emit_inst REVERT [Lit 0w; Lit 0w] [] checks = ((),se) /\
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    sf.cs_next_var = 0 /\ checks.cs_current_bb = fl /\
    checks.cs_current_insts = [] /\
    fn_has_code sf sd efn /\ fn_has_code checks se efn
Proof
  strip_tac >> drule_all run_lowering_retained_entry >> strip_tac >>
  drule compile_runtime_entry_intervals >> simp[] >> strip_tac >>
  gvs[compile_internal_fn_bodies_def, comp_return_def] >>
  drule (SRULE [cs_appends_def] cs_appends_selector_dispatch_linear) >>
  strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_external_fn_bodies) >> strip_tac >>
  `cs_extends sx sn` by metis_tac[cs_extends_new_block] >>
  `cs_extends sn se` by
    (drule emit_inst_extends >> strip_tac >> simp[cs_extends_def] >>
     qexists_tac `[]` >> simp[]) >>
  `fn_has_code sf sd efn /\ fn_has_code sn se efn` by
    metis_tac[fn_has_code_retained_interval, cs_extends_refl, cs_extends_trans] >>
  qexistsl_tac [`sf`,`sd`,`sn`,`se`] >>
  gvs[fresh_label_def, initial_compile_state_def, new_block_def]
QED

(* The emitted fallback interval includes the payable check and the body. *)
Theorem run_lowering_fallback_interval_code:
  run_lowering sels exts ints (SOME (ce,pay,nr,key,tr,view,stmts,rt))
    rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,ss,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn ==>
  ?fl sf sd opened checks st se.
    fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fl sf = ((),sd) /\
    compile_external_fn_bodies exts sd = ((),opened) /\
    new_block fl opened = (opened.cs_current_bb,checks) /\
    compile_entry_checks 4 pay checks = ((),st) /\
    compile_guarded_body ce nr key tr view stmts rt st = ((),se) /\
    cs_extends sf sd /\ cs_extends sd checks /\
    cs_extends checks st /\ cs_extends st se /\
    fn_has_code sf sd efn /\ fn_has_code checks st efn /\
    fn_has_code st se efn /\ checks.cs_current_insts = [] /\
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    sf.cs_next_var = 0
Proof
  strip_tac >> drule_all run_lowering_retained_entry >> strip_tac >>
  drule compile_runtime_entry_intervals >> simp[] >> strip_tac >>
  gvs[compile_internal_fn_bodies_def, comp_return_def] >>
  Cases_on `compile_entry_checks 4 pay sn` >>
  rename1 `compile_entry_checks 4 pay sn = (res,sk)` >> Cases_on `res` >>
  `compile_guarded_body ce nr key tr view stmts rt sk = ((),se)` by
    (qpat_x_assum `compile_fallback_body _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `compile_entry_checks _ _ _ = _` mp_tac >>
     simp[compile_fallback_body_def, compile_entry_checks_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def, ELIM_UNCURRY] >>
     strip_tac >>
     gvs[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, ELIM_UNCURRY]) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_selector_dispatch_linear) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_external_fn_bodies) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_entry_checks) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_guarded_body) >>
  `cs_extends sx sn` by metis_tac[cs_extends_new_block] >>
  `cs_extends sd sn /\ cs_extends sn se` by
    metis_tac[cs_extends_trans] >>
  `cs_extends sd se` by metis_tac[cs_extends_trans] >>
  `fn_has_code sf sd efn /\ fn_has_code sn sk efn /\
   fn_has_code sk se efn` by
    (rpt conj_tac >> irule fn_has_code_retained_interval >>
     simp[cs_extends_refl] >> qexists `se` >> simp[cs_extends_refl]) >>
  `sn.cs_current_insts = []` by
    (drule new_block_props >> simp[]) >>
  qexistsl [`fl`, `sf`, `sd`, `sx`, `sn`, `sk`, `se`] >>
  gvs[fresh_label_def, initial_compile_state_def]
QED

Theorem run_lowering_fallback_check_code:
  run_lowering sels exts ints (SOME (ce,F,nr,key,tr,view,stmts,rt))
    rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,ss,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn ==>
  ?fl sf sd sc sk.
    fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fl sf = ((),sd) /\
    compile_entry_checks 0 F sc = ((),sk) /\
    sc.cs_current_bb = fl /\ sc.cs_current_insts = [] /\
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    sf.cs_next_var = 0 /\
    fn_has_code sf sd efn /\ fn_has_code sc sk efn
Proof
  strip_tac >> drule_all run_lowering_fallback_interval_code >> strip_tac >>
  drule new_block_props >> strip_tac >>
  `compile_entry_checks 0 F checks = ((),st)` by
    fs[compile_entry_checks_def] >>
  qexistsl [`fl`, `sf`, `sd`, `checks`, `st`] >> simp[]
QED

Theorem runtime_selected_entry_code[local]:
  compile_generate_runtime sels exts [] fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),se) /\
  MEM (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) exts /\
  (!bb. MEM bb (all_blocks se) ==>
    lookup_block bb.bb_label efn.fn_blocks = SOME bb) ==>
  ?fl sf sd sc sk cenv sa sb.
    fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fl sf = ((),sd) /\
    compile_entry_checks mc pay sc = ((),sk) /\
    sc.cs_current_bb = lbl /\ sc.cs_current_insts = [] /\
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\ sf.cs_next_var = 0 /\
    fn_has_code sf sd efn /\ fn_has_code sc sk efn /\ cs_extends sd sc /\
    sd.cs_next_var <= sc.cs_next_var /\
    compile_register_positional_args ce pa 4 sk = (cenv,sa) /\
    compile_guarded_body cenv nr key tr view stmts rt sa = ((),sb) /\
    fn_has_code sa sb efn /\ fn_has_code sk sa efn /\
    cs_extends sc sk /\ cs_extends sk sa /\
    (?pre post before.
      exts = pre ++ (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt)::post /\
      compile_external_fn_bodies pre sd = ((),before) /\
      new_block lbl before = (before.cs_current_bb,sc))
Proof
  strip_tac >> drule compile_runtime_entry_intervals >> strip_tac >>
  gvs[compile_internal_fn_bodies_def, comp_return_def] >>
  drule (SRULE [cs_appends_def] cs_appends_selector_dispatch_linear) >> strip_tac >>
  drule_all external_fn_selected_check_intervals >> strip_tac >>
  `comp_ignore_bind (new_block fl)
    (case fb of NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
      | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
        compile_fallback_body ce pay nr key tr view stmts rt) sx = ((),se)` by
    simp[comp_ignore_bind_def, comp_bind_def] >>
  drule (SRULE [cs_appends_def] cs_appends_runtime_fallback_suffix) >> strip_tac >>
  `cs_extends sd se /\ cs_extends sd' se` by metis_tac[cs_extends_trans] >>
  qexistsl_tac [`fl`, `sf`, `sd`, `sc`, `sd'`, `cenv`, `sb`, `se'`] >> simp[] >>
  `cs_extends sd' sb` by
    metis_tac[cs_appends_def, cs_appends_register_positional_args] >>
  `fn_has_code sf sd efn /\ fn_has_code sc sd' efn /\ fn_has_code sb se' efn /\
   fn_has_code sd' sb efn` by
    metis_tac[fn_has_code_retained_interval, cs_extends_trans] >>
  gvs[fresh_label_def, initial_compile_state_def] >>
  qexistsl_tac [`pre`, `post`, `before`] >> simp[]
QED

Theorem run_lowering_selected_entry_code:
  run_lowering sels exts ints fb rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn /\
  MEM (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) exts ==>
  ?fl sf sd sc sk cenv sa sb.
    fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fl sf = ((),sd) /\
    compile_entry_checks mc pay sc = ((),sk) /\
    sc.cs_current_bb = lbl /\ sc.cs_current_insts = [] /\
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\ sf.cs_next_var = 0 /\
    fn_has_code sf sd efn /\ fn_has_code sc sk efn /\ cs_extends sd sc /\
    sd.cs_next_var <= sc.cs_next_var /\
    compile_register_positional_args ce pa 4 sk = (cenv,sa) /\
    compile_guarded_body cenv nr key tr view stmts rt sa = ((),sb) /\
    fn_has_code sa sb efn /\ fn_has_code sk sa efn /\
    cs_extends sc sk /\ cs_extends sk sa /\ fn_inst_ids_distinct efn /\
    (?pre post before.
      exts = pre ++ (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt)::post /\
      compile_external_fn_bodies pre sd = ((),before) /\
      new_block lbl before = (before.cs_current_bb,sc))
Proof
  strip_tac >>
  `fn_inst_ids_distinct efn` by
    (drule run_lowering_static_integrity >> strip_tac >>
     drule lookup_function_MEM >> strip_tac >>
     drule_all ctx_inst_ids_distinct_fn >>
     simp[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat,
          MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]) >>
  drule_all run_lowering_retained_entry >> strip_tac >>
  drule_all runtime_selected_entry_code >> strip_tac >>
  qexistsl_tac [`fl`, `sf`, `sd`, `sc`, `sk`, `cenv`, `sa`, `sb`] >> simp[] >>
  qexistsl_tac [`pre`, `post`, `before`] >> simp[]
QED

Theorem runtime_initial_extends[local]:
  compile_generate_runtime sels exts ints fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),sz) ==>
  cs_extends (initial_compile_state "__entry") sz
Proof
  strip_tac >> drule compile_runtime_entry_intervals >> strip_tac >>
  `comp_ignore_bind (new_block fl)
    (case fb of NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
      | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
        compile_fallback_body ce pay nr key tr view stmts rt) sx = ((),se)` by
    simp[comp_ignore_bind_def, comp_bind_def] >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_prims) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_selector_dispatch_linear) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_external_fn_bodies) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_runtime_fallback_suffix) >>
  imp_res_tac (SRULE [cs_appends_def] cs_appends_internal_fn_bodies) >>
  metis_tac[cs_extends_trans]
QED

Theorem extracted_runtime_entry_label[local]:
  cs_extends (initial_compile_state "__entry") final /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  extract_context_with_internals "__entry" ints final = SOME (ctx,data) /\
  lookup_function "__entry" ctx.ctx_functions = SOME efn ==>
  fn_entry_label efn = SOME "__entry"
Proof
  strip_tac >>
  `?bb rest. all_blocks final = bb::rest /\ bb.bb_label = "__entry"` by
    (`MAP (\bb. bb.bb_label) (all_blocks (initial_compile_state "__entry")) =
        ["__entry"]` by simp[initial_compile_state_def, all_blocks_def] >>
     drule block_labels_cs_extends >> asm_rewrite_tac[] >> strip_tac >>
     Cases_on `all_blocks final` >> gvs[]) >>
  Cases_on `package_internal_blocks (internal_fn_descriptors ints) (all_blocks final)`
  >- gvs[extract_context_with_internals_def, GSYM all_blocks_def] >>
  rename1 `package_internal_blocks _ _ = SOME p` >> PairCases_on `p` >>
  `!d. MEM d (internal_fn_descriptors ints) ==>
    ~MEM (FST d) (MAP (\b. b.bb_label) [bb])` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     `internal_label_ok (FST d)` by metis_tac[] >>
     gvs[internal_label_ok_def]) >>
  `?tail. p0 = [bb] ++ tail` by
    (irule package_internal_blocks_prefix >>
     qexistsl_tac [`internal_fn_descriptors ints`, `p1`, `rest`] >> gvs[]) >>
  drule_all extracted_entry_blocks >>
  strip_tac >> gvs[fn_entry_label_def, entry_block_def]
QED

Theorem run_lowering_entry_label:
  run_lowering sels exts ints fb rp bc mb db ei "__entry" = SOME u /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn ==>
  fn_entry_label efn = SOME "__entry"
Proof
  strip_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def] >> strip_tac >> pairarg_tac >>
  gvs[AllCaseEqs(), lowering_policy_ok_def] >>
  drule runtime_initial_extends >> strip_tac >>
  drule_all_then ACCEPT_TAC extracted_runtime_entry_label
QED

Theorem lowered_internal_package_labels[local]:
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors
    (MAP (set_internal_package_target target o
       package_internal_fn tops T (K global_nonreentrant_slot) F 0) fs))
Proof
  simp_tac pure_ss [GSYM MAP_MAP_o,
    internal_fn_descriptors_set_internal_package_target,
    internal_fn_descriptors_MAP_package_internal_fn, EVERY_MAP] >>
  simp_tac pure_ss [EVERY_MEM] >>
  qx_gen_tac `source` >> PairCases_on `source` >>
  simp_tac std_ss [source_internal_fn_descriptor_def, LET_THM, FST,
       internal_label_ok_def, internal_fn_label_prefix]
QED

Theorem lower_vyper_runtime_unit_entry_label:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn ==>
  fn_entry_label efn = SOME "__entry"
Proof
  strip_tac >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp_tac std_ss [lower_vyper_runtime_unit_def, LET_THM] >>
  pairarg_tac >> asm_simp_tac std_ss [LET_THM] >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor)` >>
  qabbrev_tac `ips = MAP
    (set_internal_package_target rpolicy.rpol_target o
     package_internal_fn tops T (K global_nonreentrant_slot) F 0)
    (order_internals (runtime_internal_order tops ints) ints)` >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ips)` by
    simp[Abbr `ips`, lowered_internal_package_labels] >>
  Cases_on `EXISTS external_has_defaults exts` >> simp[AllCaseEqs()] >> strip_tac
  >- (qpat_x_assum `run_grouped_lowering _ _ _ _ _ = _` mp_tac >>
      simp[run_grouped_lowering_def] >> strip_tac >> pairarg_tac >>
      gvs[AllCaseEqs()] >>
      `EVERY group_entry_labels_ok
        (MAP (package_external_group tops rpolicy.rpol_target T
          (K global_nonreentrant_slot)) exts)` by
        simp[EVERY_MAP, EVERY_MEM, package_external_group_labels] >>
      drule_all compile_grouped_runtime_extends >> strip_tac >>
      drule_all_then ACCEPT_TAC extracted_runtime_entry_label) >>
  drule_all_then ACCEPT_TAC run_lowering_entry_label
QED

(* These are the packages passed to the ordinary dispatcher. Their delimiters
   suffice to retain the installed code even when a body emits DALLOCA. *)
Theorem lower_vyper_runtime_legacy_packages:
  classify_functions tops = (exts,ints,fb,ctor) /\
  ~EXISTS external_has_defaults exts /\
  lower_vyper_runtime_unit tops rp = SOME unit ==>
  run_lowering
    (build_selectors (type_env tops) exts)
    (MAP (set_external_package_target rp.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot)) exts)
    (MAP (set_internal_package_target rp.rpol_target o
      package_internal_fn tops T (K global_nonreentrant_slot) F 0)
      (order_internals (runtime_internal_order tops ints) ints))
    (set_fallback_package_target rp.rpol_target
      (package_fallback_fn tops T (K global_nonreentrant_slot) fb))
    rp 0 0 []
    (build_dense_entry_info (build_selectors (type_env tops) exts)
      (MAP (set_external_package_target rp.rpol_target o
        package_external_fn tops T (K global_nonreentrant_slot)) exts))
    "__entry" = SOME unit /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl)
    (MAP (set_external_package_target rp.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot)) exts) /\
  EVERY (\d. internal_label_ok (FST d))
    (internal_fn_descriptors
      (MAP (set_internal_package_target rp.rpol_target o
        package_internal_fn tops T (K global_nonreentrant_slot) F 0)
        (order_internals (runtime_internal_order tops ints) ints)))
Proof
  strip_tac >> rpt conj_tac
  >- (qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
      simp[lower_vyper_runtime_unit_def, AllCaseEqs()])
  >- (rw[EVERY_MAP, EVERY_MEM] >> PairCases_on `x` >>
      simp[package_external_fn_def, set_external_package_target_def,
           jump_label_ok_def]) >>
  simp[lowered_internal_package_labels]
QED

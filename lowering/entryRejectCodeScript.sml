Theory entryRejectCode
Ancestors
  entryCodeOwnership entryRawFunction moduleLowering compileEnv list pair
  loweringShapeProps loweringShapeDefs loweringShapeRules vyperCompiler venomInst
  entryBodyBoundLabels entryCompileIntervals entryInternalAppend entryLinearAppend
  entryPrefixRetention fragExec venomExecProofs
  allocaFrontierBound venomWf removeUnusedSsaProofs venomWfProps

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
  ?se. compile_generate_runtime sels exts [] fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),se) /\
    (!bb. MEM bb (all_blocks se) ==> MEM bb eb)
Proof
  strip_tac >> drule compile_runtime_without_internals_prefix >> strip_tac >>
  `!d. MEM d (internal_fn_descriptors ints) ==>
    ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks se))` by
    (metis_tac[runtime_entry_delimiter_exclusion]) >>
  drule internal_fn_bodies_all_blocks_prefix >> strip_tac >>
  qexists_tac `se` >> simp[] >> rpt strip_tac >>
  irule package_internal_blocks_prefix_mem >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
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
  qexists_tac `se` >> simp[] >> rpt strip_tac >>
  irule MEM_lookup_block >> gvs[]
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
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    fn_has_code sf sd efn /\ fn_has_code sc sk efn /\ cs_extends sd sc /\
    sd.cs_next_var <= sc.cs_next_var /\
    compile_register_positional_args ce pa 4 sk = (cenv,sa) /\
    compile_guarded_body cenv nr key tr view stmts rt sa = ((),sb) /\
    fn_has_code sa sb efn
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
  `fn_has_code sf sd efn /\ fn_has_code sc sd' efn /\ fn_has_code sb se' efn` by
    (metis_tac[fn_has_code_retained_interval, cs_extends_trans]) >>
  gvs[fresh_label_def, initial_compile_state_def]
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
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    fn_has_code sf sd efn /\ fn_has_code sc sk efn /\ cs_extends sd sc /\
    sd.cs_next_var <= sc.cs_next_var /\
    compile_register_positional_args ce pa 4 sk = (cenv,sa) /\
    compile_guarded_body cenv nr key tr view stmts rt sa = ((),sb) /\
    fn_has_code sa sb efn /\ fn_inst_ids_distinct efn
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
  qexistsl_tac [`fl`, `sf`, `sd`, `sc`, `sk`, `cenv`, `sa`, `sb`] >> simp[]
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

Theorem runtime_first_block[local]:
  compile_generate_runtime sels exts ints fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),sz) ==>
  ?bb rest. all_blocks sz = bb::rest /\ bb.bb_label = "__entry"
Proof
  strip_tac >> drule runtime_initial_extends >> strip_tac >>
  `MAP (\bb. bb.bb_label) (all_blocks (initial_compile_state "__entry")) =
    ["__entry"]` by simp[initial_compile_state_def, all_blocks_def] >>
  drule block_labels_cs_extends >> asm_rewrite_tac[] >> strip_tac >>
  Cases_on `all_blocks sz` >> gvs[]
QED

Theorem runtime_packaged_first_block[local]:
  compile_generate_runtime sels exts ints fb Linear bc mb db ei
    (initial_compile_state "__entry") = ((),sz) /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  package_internal_blocks (internal_fn_descriptors ints) (all_blocks sz) =
    SOME (eb,fs) ==>
  ?bb rest. eb = bb::rest /\ bb.bb_label = "__entry"
Proof
  strip_tac >> drule runtime_first_block >> strip_tac >>
  `!d. MEM d (internal_fn_descriptors ints) ==>
    ~MEM (FST d) (MAP (\b. b.bb_label) [bb])` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     `internal_label_ok (FST d)` by metis_tac[] >>
     gvs[internal_label_ok_def]) >>
  `?tail. eb = [bb] ++ tail` by
    (irule package_internal_blocks_prefix >> simp[] >>
     qexistsl_tac [`internal_fn_descriptors ints`, `fs`, `rest`] >> gvs[]) >>
  gvs[]
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
  qpat_assum `extract_context_with_internals _ _ _ = _`
    (mp_tac o REWRITE_RULE [extract_context_with_internals_def]) >>
  strip_tac >> gvs[AllCaseEqs()] >> fs[GSYM all_blocks_def] >>
  drule_all runtime_packaged_first_block >> strip_tac >>
  drule_all extracted_entry_blocks >>
  simp[fn_entry_label_def, entry_block_def] >> strip_tac >> simp[]
QED

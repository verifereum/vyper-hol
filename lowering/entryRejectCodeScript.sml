Theory entryRejectCode
Ancestors
  entryCodeOwnership entryRawFunction moduleLowering compileEnv list pair
  loweringShapeProps loweringShapeDefs loweringShapeRules vyperCompiler venomInst

Theorem compile_external_fn_bodies_append[local]:
  !xs ys.
  compile_external_fn_bodies (xs ++ ys) =
  comp_ignore_bind (compile_external_fn_bodies xs)
                   (compile_external_fn_bodies ys)
Proof
  Induct
  >- simp[compile_external_fn_bodies_def, comp_ignore_bind_def,
          FUN_EQ_THM, comp_bind_def, comp_return_def] >>
  qx_gen_tac `h` >> PairCases_on `h` >>
  simp[compile_external_fn_bodies_def, comp_ignore_bind_def, comp_bind_def,
       FUN_EQ_THM] >> rpt gen_tac >> rpt (pairarg_tac >> simp[])
QED

Theorem compile_external_fn_bodies_selected_checks[local]:
  MEM (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) fns /\
  compile_external_fn_bodies fns sa = ((),sz) ==>
  ?pre post sp sc sd sb.
    fns = pre ++ (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt)::post /\
    compile_external_fn_bodies pre sa = ((),sp) /\
    new_block lbl sp = (sp.cs_current_bb,sc) /\
    compile_entry_checks mc pay sc = ((),sd) /\
    compile_external_function_body ce pa nr key tr view stmts rt sd = ((),sb) /\
    compile_external_fn_bodies post sb = ((),sz)
Proof
  strip_tac >>
  drule (iffLR MEM_SPLIT) >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_external_fn_bodies _ _ = _` mp_tac >>
  simp[compile_external_fn_bodies_append, compile_external_fn_bodies_def,
       comp_ignore_bind_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  qexistsl_tac [`l1`, `l2`] >> simp[] >>
  rpt (goal_assum (drule_at Any)) >> gvs[new_block_def]
QED

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

Theorem compile_runtime_retained_entry_stream[local]:
  compile_generate_runtime sels exts ints fb Linear buckets meta dense info
    (initial_compile_state "__entry") = ((),sz) /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY external_fn_shape_ok exts /\ fallback_shape_ok fb /\
  EVERY internal_fn_shape_ok ints ==>
  ?se segs.
    compile_generate_runtime sels exts [] fb Linear buckets meta dense info
      (initial_compile_state "__entry") = ((),se) /\
    compile_internal_fn_bodies ints se = ((),sz) /\
    shape_state se /\
    all_blocks sz = all_blocks se ++ FLAT segs /\
    all_blocks se <> [] /\ (HD (all_blocks se)).bb_label = "__entry" /\
    EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks se))) /\
    LIST_REL internal_segment_ok (internal_fn_descriptors ints) segs
Proof
  strip_tac >> drule compile_runtime_without_internals_prefix >> strip_tac >>
  `EVERY internal_fn_shape_ok []` by simp[] >>
  qpat_assum `compile_generate_runtime _ _ [] _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac compile_generate_runtime_shape) >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[internal_fn_descriptors_def] >>
  drule_all compile_internal_fn_bodies_shape >> strip_tac >>
  qexists_tac `segs` >> simp[]
QED

Theorem compile_runtime_retained_entry_package[local]:
  compile_generate_runtime sels exts ints fb Linear buckets meta dense info
    (initial_compile_state "__entry") = ((),sz) /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY external_fn_shape_ok exts /\ fallback_shape_ok fb /\
  EVERY internal_fn_shape_ok ints /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors ints)) ==>
  ?se fs.
    compile_generate_runtime sels exts [] fb Linear buckets meta dense info
      (initial_compile_state "__entry") = ((),se) /\
    compile_internal_fn_bodies ints se = ((),sz) /\
    shape_state se /\
    package_internal_blocks (internal_fn_descriptors ints) (all_blocks sz) =
      SOME (all_blocks se,fs)
Proof
  strip_tac >> drule_all compile_runtime_retained_entry_stream >> strip_tac >>
  `EVERY (\d. ~compiler_label (FST d) /\
               ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks se)))
         (internal_fn_descriptors ints)` by
    (pure_rewrite_tac[EVERY_MEM] >> gen_tac >> disch_tac >> BETA_TAC >>
     irule internal_name_not_entry_label >> simp[] >>
     gvs[EVERY_MEM]) >>
  drule_all package_internal_blocks_segments >> strip_tac >>
  qexists_tac `se` >> simp[]
QED

Theorem run_lowering_retained_entry[local]:
  run_lowering sels exts ints fb rp buckets meta dense info "__entry" = SOME u /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY external_fn_shape_ok exts /\ fallback_shape_ok fb /\
  EVERY internal_fn_shape_ok ints /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors ints)) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn ==>
  ?se.
    compile_generate_runtime sels exts [] fb Linear buckets meta dense info
      (initial_compile_state "__entry") = ((),se) /\
    shape_state se /\ efn.fn_blocks = all_blocks se /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se))
Proof
  strip_tac >>
  `lowering_context_ok u.cu_context` by metis_tac[run_lowering_context_ok] >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def] >> strip_tac >> pairarg_tac >>
  gvs[AllCaseEqs(), lowering_policy_ok_def] >>
  drule compile_runtime_retained_entry_package >>
  (impl_tac >- simp[]) >> strip_tac >>
  `efn.fn_blocks = all_blocks se` by
    (drule_all extracted_entry_blocks >> simp[]) >>
  qexists_tac `se` >> simp[] >>
  drule lowering_context_ok_bridge >> strip_tac >>
  `MEM efn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  gvs[EVERY_MEM, fn_labels_def] >> metis_tac[]
QED

Theorem shape_step_run_extends[local]:
  shape_step internal lp (\s. T) m (\x s. T) /\
  m a = ((),b) /\ shape_state a ==>
  cs_extends a b /\ shape_state b
Proof
  simp[shape_step_def, shape_extends_def] >> metis_tac[]
QED

Theorem compile_external_checks_shape_interval[local]:
  EVERY external_fn_shape_ok pre /\ shape_state sa /\
  compile_external_fn_bodies pre sa = ((),sp) /\
  new_block lbl sp = (sp.cs_current_bb,sc) /\
  compile_entry_checks mc pay sc = ((),sd) ==>
  cs_extends sa sc /\ cs_extends sc sd /\ shape_state sc /\ shape_state sd
Proof
  strip_tac >>
  `cs_extends sa sp /\ shape_state sp` by
    (irule shape_step_run_extends >> conj_tac >- simp[] >>
     qexistsl_tac [`F`, `jump_label_ok`, `compile_external_fn_bodies pre`] >>
     simp[compile_external_fn_bodies_shape]) >>
  `shape_state sc` by metis_tac[shape_state_new_block] >>
  `cs_extends sp sc` by metis_tac[cs_extends_new_block] >>
  `cs_extends sc sd /\ shape_state sd` by
    (irule shape_step_run_extends >> conj_tac >- simp[] >>
     qexistsl_tac [`F`, `compiler_label`, `compile_entry_checks mc pay`] >>
     simp[compile_entry_checks_shape]) >>
  metis_tac[cs_extends_trans]
QED

Theorem compile_external_checks_suffix_shape[local]:
  external_fn_shape_ok (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) /\
  EVERY external_fn_shape_ok post /\ shape_state sd /\
  compile_external_function_body ce pa nr key tr view stmts rt sd = ((),sb) /\
  compile_external_fn_bodies post sb = ((),sx) ==>
  cs_extends sd sx /\ shape_state sx
Proof
  strip_tac >>
  `cs_extends sd sb /\ shape_state sb` by
    (irule shape_step_run_extends >> conj_tac >- simp[] >>
     qexistsl_tac [`F`, `compiler_label`,
       `compile_external_function_body ce pa nr key tr view stmts rt`] >>
     gvs[external_fn_shape_ok_def] >>
     simp[compile_external_function_body_shape]) >>
  `cs_extends sb sx /\ shape_state sx` by
    (irule shape_step_run_extends >> conj_tac >- simp[] >>
     qexistsl_tac [`F`, `jump_label_ok`, `compile_external_fn_bodies post`] >>
     simp[compile_external_fn_bodies_shape]) >>
  metis_tac[cs_extends_trans]
QED

Theorem compile_external_selected_checks_intervals[local]:
  MEM (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) fns /\
  EVERY external_fn_shape_ok fns /\ shape_state sa /\
  compile_external_fn_bodies fns sa = ((),sx) ==>
  ?sc sd.
    compile_entry_checks mc pay sc = ((),sd) /\
    sc.cs_current_bb = lbl /\ sc.cs_current_insts = [] /\
    cs_extends sa sc /\ cs_extends sc sd /\ cs_extends sd sx /\
    shape_state sc /\ shape_state sd /\ shape_state sx
Proof
  strip_tac >> drule_all compile_external_fn_bodies_selected_checks >>
  strip_tac >>
  `EVERY external_fn_shape_ok pre /\
   external_fn_shape_ok (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) /\
   EVERY external_fn_shape_ok post` by gvs[EVERY_APPEND] >>
  drule_all compile_external_checks_shape_interval >> strip_tac >>
  drule_all compile_external_checks_suffix_shape >> strip_tac >>
  qexistsl_tac [`sc`, `sd`] >> gvs[new_block_def]
QED

Theorem compile_runtime_fallback_suffix_extends[local]:
  shape_state sx /\ fallback_shape_ok fb /\
  new_block fl sx = (sx.cs_current_bb,sn) /\
  (case fb of
     NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
   | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
       compile_fallback_body ce pay nr key tr view stmts rt) sn = ((),se) ==>
  cs_extends sx se
Proof
  strip_tac >>
  `cs_extends sx sn` by metis_tac[cs_extends_new_block] >>
  `shape_state sn` by metis_tac[shape_state_new_block] >>
  `cs_extends sn se` suffices_by metis_tac[cs_extends_trans] >>
  Cases_on `fb`
  >- (gvs[] >> metis_tac[fragExecTheory.cs_extends_emit_inst]) >>
  PairCases_on `x` >> gvs[] >>
  irule (cj 1 shape_step_run_extends) >> conj_tac >- simp[] >>
  qexistsl_tac [`F`, `compiler_label`,
    `compile_fallback_body x0 x1 x2 x3 x4 x5 x6 x7`] >>
  simp[compile_fallback_body_shape]
QED

Theorem compile_dispatch_prefix_shape[local]:
  shape_state sa /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  fresh_label "fallback" sa = (fl,sf) /\
  compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
    fl sf = ((),sd) ==>
  cs_extends sa sf /\ cs_extends sf sd /\ shape_state sf /\ shape_state sd
Proof
  strip_tac >>
  mp_tac (Q.SPECL [`F`, `jump_label_ok`, `\s. T`, `"fallback"`]
    shape_step_fresh_label_sfx) >>
  simp[shape_stable_def, shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  `~label_sfx "dispatch" fl` by
    (`"fallback" <> "dispatch"` by EVAL_TAC >>
     metis_tac[label_sfx_distinct]) >>
  `EVERY (\(sel,lbl). jump_label_ok lbl)
     (MAP (\(sel,lbl,z). (sel,lbl)) sels)` by
    (gvs[EVERY_MAP, EVERY_MEM, FORALL_PROD, jump_label_ok_def] >>
     metis_tac[]) >>
  `cs_extends sf sd /\ shape_state sd` by
    (irule shape_step_run_extends >> conj_tac >- simp[] >>
     qexistsl_tac [`F`, `jump_label_ok`,
       `compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels) fl`] >>
     simp[compile_selector_dispatch_linear_shape, jump_label_ok_def]) >>
  gvs[shape_extends_def]
QED

Theorem compile_runtime_selected_entry_code[local]:
  compile_generate_runtime sels exts [] fb Linear buckets meta dense info
    (initial_compile_state "__entry") = ((),se) /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY external_fn_shape_ok exts /\ fallback_shape_ok fb /\
  MEM (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) exts /\
  efn.fn_blocks = all_blocks se /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se)) ==>
  ?fl sf sd sc sk.
    fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fl sf = ((),sd) /\
    compile_entry_checks mc pay sc = ((),sk) /\
    sc.cs_current_bb = lbl /\ sc.cs_current_insts = [] /\
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    fn_has_code sf sd efn /\ fn_has_code sc sk efn
Proof
  strip_tac >> drule compile_runtime_entry_intervals >> strip_tac >>
  gvs[compile_internal_fn_bodies_def, comp_return_def] >>
  `shape_state (initial_compile_state "__entry")` by
    simp[initial_compile_state_def, shape_state_def, shape_base_state_def,
         raw_checked_state_def, raw_checked_blocks_def, opaque_insts_ok_def,
         state_insts_def, all_blocks_def] >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels` by simp[] >>
  `fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf)` by simp[] >>
  qpat_x_assum `(_,_) = fresh_label _ _` kall_tac >>
  drule_all compile_dispatch_prefix_shape >> strip_tac >>
  drule_all compile_external_selected_checks_intervals >> strip_tac >>
  drule_all compile_runtime_fallback_suffix_extends >> strip_tac >>
  `cs_extends sd se` by metis_tac[cs_extends_trans] >>
  `cs_extends sd' se` by metis_tac[cs_extends_trans] >>
  qexistsl_tac [`fl`, `sf`, `sd`, `sc`, `sd'`] >> simp[] >>
  `fn_has_code sf sd efn` by
    (irule fn_has_code_distinct_endpoint >> conj_tac >- simp[] >>
     qexists_tac `se` >> simp[]) >>
  `fn_has_code sc sd' efn` by
    (irule fn_has_code_distinct_endpoint >> conj_tac >- simp[] >>
     qexists_tac `se` >> simp[]) >>
  gvs[fresh_label_def, initial_compile_state_def]
QED

Theorem run_lowering_selected_entry_code:
  run_lowering sels exts ints fb rp buckets meta dense info "__entry" = SOME u /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY external_fn_shape_ok exts /\ fallback_shape_ok fb /\
  EVERY internal_fn_shape_ok ints /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors ints)) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn /\
  MEM (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) exts ==>
  ?fl sf sd sc sk.
    fresh_label "fallback" (initial_compile_state "__entry") = (fl,sf) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fl sf = ((),sd) /\
    compile_entry_checks mc pay sc = ((),sk) /\
    sc.cs_current_bb = lbl /\ sc.cs_current_insts = [] /\
    sf.cs_current_bb = "__entry" /\ sf.cs_current_insts = [] /\
    fn_has_code sf sd efn /\ fn_has_code sc sk efn
Proof
  strip_tac >> drule_all run_lowering_retained_entry >> strip_tac >>
  drule_all compile_runtime_selected_entry_code >> strip_tac >>
  qexistsl_tac [`fl`, `sf`, `sd`, `sc`, `sk`] >> simp[]
QED

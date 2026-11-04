Theory entryRejectCode
Ancestors
  entryCodeOwnership entryRawFunction moduleLowering compileEnv list pair
  loweringShapeProps vyperCompiler

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

Theorem compile_external_fn_bodies_selected_checks:
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

Theorem compile_runtime_entry_intervals:
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

Theorem compile_runtime_without_internals_prefix:
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

Theorem compile_runtime_retained_entry_stream:
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

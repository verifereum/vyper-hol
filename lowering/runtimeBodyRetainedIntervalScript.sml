(* Retention of a selected external body in a lowered entry function. *)
Theory runtimeBodyRetainedInterval
Ancestors
  entryRejectCode actualRegistrationCode actualDecoderPackaging
  entryCodeOwnership entryCompileIntervals
  moduleLowering compileVyper vyperCompiler loweringShapeDefs
  rawEntryCode loweringShapeProps compileEnv fragExec venomInst list

val _ = Parse.hide "body";

Theorem run_lowering_entry_coverage:
  run_lowering sels packs ints fall rp buckets metadata dense info "__entry" =
    SOME unit /\
  EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl) packs /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) ==>
  ?func entry_end.
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    MEM func unit.cu_context.ctx_functions /\
    compile_generate_runtime sels packs [] fall Linear buckets metadata
      dense info (initial_compile_state "__entry") = ((),entry_end) /\
    (!bb. MEM bb (all_blocks entry_end) ==>
      lookup_block bb.bb_label func.fn_blocks = SOME bb)
Proof
  strip_tac >>
  `?func. lookup_function "__entry" unit.cu_context.ctx_functions = SOME func` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[run_lowering_def] >> strip_tac >> pairarg_tac >>
     gvs[AllCaseEqs()] >>
     qpat_x_assum `extract_context_with_internals _ _ _ = _` mp_tac >>
     simp[extract_context_with_internals_def, AllCaseEqs()] >>
     strip_tac >> gvs[mk_venom_context_def, mk_raw_function_def,
                      lookup_function_def, listTheory.FIND_thm]) >>
  drule_all run_lowering_retained_entry >> strip_tac >>
  qexistsl_tac [`func`, `se`] >> simp[] >>
  metis_tac[lookup_function_MEM]
QED

Theorem run_lowering_pinned_body_interval:
  run_lowering sels (pre ++ (lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt)::post)
    ints fb rp buckets metadata dense info "__entry" = SOME unit /\
  EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl)
    (pre ++ (lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt)::post) /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  fresh_label "fallback" (initial_compile_state "__entry") = (fl,ls) /\
  compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
    fl ls = ((),ds) /\
  compile_external_fn_bodies pre ds = ((),opened) /\
  new_block lbl opened = (opened.cs_current_bb,checks) /\
  compile_entry_checks mincd pay checks = ((),st) /\
  compile_register_positional_args ce pos 4 st = (cenv,sa) /\
  compile_guarded_body cenv nr key ut iv body rt sa = ((),st') ==>
  ?func.
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    MEM func unit.cu_context.ctx_functions /\
    fn_has_code sa st' func
Proof
  strip_tac >> drule_all run_lowering_entry_coverage >> strip_tac >>
  drule runtime_external_internal_phase_split >> strip_tac >>
  gvs[compile_internal_fn_bodies_def, comp_return_def] >>
  `compile_external_function_body ce pos nr key ut iv body rt st = ((),st')` by
    simp[compile_external_function_body_def, comp_bind_def] >>
  `compile_external_fn_bodies
    [(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt)] opened = ((),st')` by
    simp[compile_external_fn_bodies_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def] >>
  `compile_external_fn_bodies post st' = ((),external_st)` by
    (qpat_x_assum `compile_external_fn_bodies (_ ++ _) _ = _` mp_tac >>
     rewrite_tac[external_bodies_append] >> strip_tac >> gvs[] >>
     qpat_x_assum `compile_external_fn_bodies (_::_) _ = _` mp_tac >>
     pure_once_rewrite_tac[external_bodies_cons_split] >> strip_tac >> gvs[]) >>
  rename1 `new_block fallback_lbl external_st = (_,fallback_st)` >>
  `comp_ignore_bind (new_block fallback_lbl)
    (case fb of NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
      | SOME (ce,pay,nr,key,ut,iv,body,rt) =>
        compile_fallback_body ce pay nr key ut iv body rt) external_st =
    ((),entry_end)` by
    simp[comp_ignore_bind_def, comp_bind_def] >>
  `cs_extends sa st'` by metis_tac[cs_appends_def, cs_appends_guarded_body] >>
  `cs_extends st' external_st` by
    metis_tac[cs_appends_def, cs_appends_external_fn_bodies] >>
  `cs_extends external_st entry_end` by
    metis_tac[cs_appends_def, cs_appends_runtime_fallback_suffix] >>
  metis_tac[cs_extends_trans, fn_has_code_retained_interval]
QED

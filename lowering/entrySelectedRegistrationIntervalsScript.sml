(* Joint ownership of the selected checks, registration, and guarded body. *)
Theory entrySelectedRegistrationIntervals
Ancestors
  entryRejectCode entryRuntimePrefix entryCompileIntervals entryCodeOwnership
  entryRawFunction entryLinearAppend fragExec compileEnv moduleLowering loweringShapeDefs
  vyperCompiler venomInst venomExecProofs allocaFrontierBound venomWf
  removeUnusedSsaProofs list pair

Theorem runtime_selected_registration_intervals[local]:
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
    fn_has_code sa sb efn /\ fn_has_code sk sa efn /\
    fn_has_code sk sb efn /\ cs_extends sk sa
Proof
  strip_tac >> drule compile_generate_runtime_linear_split >> strip_tac >>
  gvs[compile_internal_fn_bodies_def, comp_return_def] >>
  drule (SRULE [cs_appends_def] cs_appends_selector_dispatch_linear) >> strip_tac >>
  drule_all external_fn_selected_check_intervals >> strip_tac >>
  `comp_ignore_bind (new_block fallback_lbl)
    (case fb of NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
      | SOME (ce,pay,nr,key,tr,view,stmts,rt) =>
          compile_fallback_body ce pay nr key tr view stmts rt) s3 = ((),entry_st)` by
    gvs[comp_ignore_bind_def, comp_bind_def] >>
  drule (SRULE [cs_appends_def] cs_appends_runtime_fallback_suffix) >> strip_tac >>
  drule (SRULE [cs_appends_def] cs_appends_register_positional_args) >> strip_tac >>
  qexistsl [`fallback_lbl`, `s1`, `s2`, `sc`, `sd`, `cenv`, `sb`, `se`] >>
  simp[] >>
  `fn_has_code s1 s2 efn /\ fn_has_code sc sd efn /\
   fn_has_code sb se efn /\ fn_has_code sd sb efn /\
   fn_has_code sd se efn` by
    metis_tac[fn_has_code_retained_interval, cs_extends_trans] >>
  gvs[fresh_label_def, initial_compile_state_def]
QED

Theorem run_lowering_selected_registration_intervals:
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
    fn_has_code sa sb efn /\ fn_inst_ids_distinct efn /\
    fn_has_code sk sa efn /\ fn_has_code sk sb efn /\ cs_extends sk sa
Proof
  strip_tac >>
  `fn_inst_ids_distinct efn` by
    (drule run_lowering_static_integrity >> strip_tac >>
     drule lookup_function_MEM >> strip_tac >>
     drule_all ctx_inst_ids_distinct_fn >>
     simp[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat,
          MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]) >>
  drule_all run_lowering_retained_entry >> strip_tac >>
  drule_all runtime_selected_registration_intervals >> strip_tac >>
  qexistsl [`fl`, `sf`, `sd`, `sc`, `sk`, `cenv`, `sa`, `sb`] >> simp[]
QED

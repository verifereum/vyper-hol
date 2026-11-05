(* Selected guarded-body ownership without body-shape restrictions. *)
Theory entrySelectedOwnership
Ancestors
  entrySelectedIntervals entryRejectCode entryCodeOwnership entrySourcePackages
  entryRuntimeSlice compileEnv compileVyper supportedProgram supportedDecls
  e2eDefs list fragExec allocaFrontierBound venomWf removeUnusedSsaProofs
  venomInst vyperCompiler loweringShapeDefs

Theorem run_lowering_selected_guarded_code[local]:
  run_lowering sels exts ints fb rp bc mb db ei "__entry" = SOME u /\
  EVERY (\(lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt). jump_label_ok lbl) exts /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  MEM (lbl,ce,pa,mc,pay,nr,key,tr,view,stmts,rt) exts /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn ==>
  ?sd cenv sa se.
    compile_register_positional_args ce pa 4 sd = (cenv,sa) /\
    compile_guarded_body cenv nr key tr view stmts rt sa = ((),se) /\
    fn_has_code sa se efn /\ fn_inst_ids_distinct efn
Proof
  strip_tac >> drule_all run_lowering_selected_entry_code >> strip_tac >>
  qexistsl [`sk`, `cenv`, `sa`, `sb`] >> simp[]
QED

Theorem source_selected_guarded_code:
  lower_vyper_runtime_unit tops rp = SOME u /\ supported_program tops /\
  valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  lookup_function "__entry" u.cu_context.ctx_functions = SOME efn ==>
  ?lbl ce pa mc pay key tr view rt sd cenv sa se.
    set_external_package_target rp.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut,F,lookup_raw_return_or_F (NONE : num option)
          tx.function_name External tops,tx.function_name,args,([] : expr list),ret,fbody)) =
      (lbl,ce,pa,mc,pay,F,key,tr,view,fbody,rt) /\
    compile_register_positional_args ce pa 4 sd = (cenv,sa) /\
    compile_guarded_body cenv F key tr view fbody rt sa = ((),se) /\
    fn_has_code sa se efn /\ fn_inst_ids_distinct efn
Proof
  strip_tac >>
  `MEM (mut,F,lookup_raw_return_or_F (NONE : num option)
     tx.function_name External tops,tx.function_name,args,([] : expr list),ret,fbody)
     (FST (classify_functions tops))` by
    (irule supported_external_lookup_classified >>
     conj_tac >- gvs[valid_vyper_call_def] >>
     simp[] >> qexists `tops` >>
     gvs[supported_program_def, supported_declaration_headers_def]) >>
  drule_all lower_runtime_selected_source_packages >> strip_tac >>
  qabbrev_tac `pkg = set_external_package_target rp.rpol_target
    (package_external_fn tops F (assign_nkeys tops 0)
      (mut,F,lookup_raw_return_or_F (NONE : num option)
        tx.function_name External tops,tx.function_name,args,([] : expr list),ret,fbody))` >>
  `MEM pkg exts` by
    (gvs[Abbr `pkg`] >> rewrite_tac[MEM_MAP] >>
     qexists `(mut,F,lookup_raw_return_or_F (NONE : num option)
       tx.function_name External tops,tx.function_name,args,([] : expr list),ret,fbody)` >>
     conj_tac >- (rewrite_tac[combinTheory.o_THM] >> REFL_TAC) >> first_assum ACCEPT_TAC) >>
  PairCases_on `pkg` >>
  `pkg5 = F /\ pkg9 = fbody` by
    (fs[markerTheory.Abbrev_def] >>
     gvs[package_external_fn_def, set_external_package_target_def]) >>
  gvs[] >> drule_all run_lowering_selected_guarded_code >> strip_tac >>
  qexistsl [`sd`,`cenv`,`sa`,`se`] >> simp[]
QED

Theory entryReachBodyCanonicalChecks
Ancestors
  loweringStateRelDefs entryReachBodyCanonicalOccurrence entryReachBodySelectedCode
  externalEntryChecks moduleLoweringProps vyperCompiler venomInst
  loweringShapeDefs compileEnv selectedBodyCode venomWf moduleLowering
  loweringShapeProps compileVyper vyperLoweringCorrect entryDispatchProps
  venomState venomExecSemantics entryChecksProps entryRegistrationOpen list pair
Libs
  monadsyntax

Theorem entry_runtime_lookup_raw[local]:
  run_lowering selectors packages internals fallback policy
    buckets metadata dense info "__entry" = SOME unit /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func ==>
  func = mk_raw_function "__entry" func.fn_blocks
Proof
  Cases_on `compile_generate_runtime selectors packages internals fallback
    policy.rpol_frontend_dispatch buckets metadata dense info
    (initial_compile_state "__entry")` >>
  rename1 `_ = (u,final)` >> Cases_on `u` >>
  simp[run_lowering_def, extract_context_with_internals_def,
       AllCaseEqs()] >> rpt strip_tac >>
  gvs[mk_venom_context_def, venomInstTheory.lookup_function_def,
      mk_raw_function_def, FIND_thm]
QED

Theorem entry_runtime_canonical_code[local]:
  run_lowering selectors packages internals fallback policy
    buckets metadata dense info "__entry" = SOME unit /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY (\p. isPREFIX "fn_" (FST p)) packages /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internals) /\
  ALL_DISTINCT (MAP FST packages) /\ ~isPREFIX "@" lbl /\
  isPREFIX "fn_" lbl /\
  MEM (lbl,ce,args,mincd,pay,nr,key,ut,iv,fbody,rt) packages ==>
  ?func se fb label_st dispatch_st checks start cenv registered body_end.
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    func = mk_raw_function "__entry" (all_blocks se) /\
    func.fn_blocks <> [] /\ (HD func.fn_blocks).bb_label = "__entry" /\
    fn_inst_ids_distinct func /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fb,label_st) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors)
      fb label_st = ((),dispatch_st) /\ fn_has_code label_st dispatch_st func /\
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce args 4 start = (cenv,registered) /\
    compile_guarded_body cenv nr key ut iv fbody rt registered = ((),body_end) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    dispatch_st.cs_next_var <= checks.cs_next_var /\
    cs_extends start registered /\ cs_extends registered body_end /\
    cs_extends body_end se /\
    fn_has_code checks start func /\ fn_has_code start body_end func /\
    fn_has_code registered body_end func /\
    (!inst. MEM inst (state_insts registered) ==> MEM inst (fn_insts func))
Proof
  strip_tac >> drule_all run_lowering_entry_function_labels >> strip_tac >>
  `func = mk_raw_function "__entry" (all_blocks se)` by
    (drule_all entry_runtime_lookup_raw >> simp[]) >>
  `EVERY (\(sel,lbl). jump_label_ok lbl)
     (MAP (\(sel,lbl,z). (sel,lbl)) selectors)` by
    (gvs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
         loweringShapeDefsTheory.jump_label_ok_def] >> metis_tac[]) >>
  drule_all runtime_entry_dispatch_code_labels >> strip_tac >>
  `~MEM lbl (MAP (\bb. bb.bb_label) (all_blocks sd))` by
    (qpat_x_assum `!l. l IN bound_labels sd ==> _` (qspec_then `lbl` mp_tac) >>
     simp[bound_labels_def, all_blocks_def, MAP_REVERSE]) >>
  `MEM func unit.cu_context.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  `fn_inst_ids_distinct func` by
    (drule run_lowering_static_integrity >> strip_tac >>
     qpat_x_assum `MEM func _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
     gvs[venomWfTheory.ctx_inst_ids_distinct_def, venomWfTheory.fn_inst_ids_distinct_def,
         MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se))` by
    (drule run_lowering_context_ok >>
     simp[lowering_context_ok_def, EVERY_MEM] >> strip_tac >>
     qpat_x_assum `!fn. MEM fn _ ==> ALL_DISTINCT _ /\ _`
       (qspec_then `func` mp_tac) >>
     simp[venomInstTheory.fn_labels_def]) >>
  drule_all entry_canonical_occurrence_code >> strip_tac >>
  qexistsl_tac [`func`,`se`,`fb`,`sa`,`sd`,`checks`,`start`,`cenv`,
    `registered`,`body_end`] >> simp[]
QED

Theorem entry_source_canonical_phase[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  MEM (mut,F,rr,name,args,[],ret,fbody) (FST (classify_functions tops)) /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops F (assign_nkeys tops 0)
      (mut,F,rr,name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) /\
  isPREFIX "fn_" lbl /\ ~isPREFIX "@" lbl ==>
  ?func se fb label_st dispatch_st checks start cenv registered body_end.
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    func = mk_raw_function "__entry" (all_blocks se) /\
    func.fn_blocks <> [] /\ (HD func.fn_blocks).bb_label = "__entry" /\
    fn_inst_ids_distinct func /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fb,label_st) /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb label_st = ((),dispatch_st) /\ fn_has_code label_st dispatch_st func /\
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce pos 4 start = (cenv,registered) /\
    compile_guarded_body cenv F key ut iv fbody rt registered = ((),body_end) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    dispatch_st.cs_next_var <= checks.cs_next_var /\
    cs_extends start registered /\ cs_extends registered body_end /\
    cs_extends body_end se /\
    fn_has_code checks start func /\ fn_has_code start body_end func /\
    fn_has_code registered body_end func /\
    (!inst. MEM inst (state_insts registered) ==> MEM inst (fn_insts func))
Proof
  strip_tac >>
  `ALL_DISTINCT (supported_function_names tops)` by
    gvs[supportedProgramTheory.supported_program_def,
        supportedNamesTheory.supported_declaration_names_def] >>
  drule classified_external_labels_distinct >> disch_tac >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fallback,ctor)` >>
  simp[] >> strip_tac >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl)
     (build_selectors (type_env tops) exts)` by
    simp[loweringShapePropsTheory.build_selectors_fn_labels] >>
  qmatch_asmsub_abbrev_tac `run_lowering selectors packages internal_fns fallback_fn` >>
  `EVERY (\p. isPREFIX "fn_" (FST p)) packages` by
    simp[Abbr `packages`, EVERY_MAP, EVERY_MEM, FORALL_PROD,
         set_external_package_target_def, package_external_fn_def, LET_THM] >>
  `ALL_DISTINCT (MAP FST packages)` by
    gvs[Abbr `packages`, MAP_MAP_o, combinTheory.o_DEF,
        pairTheory.LAMBDA_PROD, set_external_package_target_def,
        package_external_fn_def, LET_THM] >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns)` by
    (simp_tac std_ss [Abbr `internal_fns`, GSYM MAP_MAP_o,
          internal_fn_descriptors_set_internal_package_target,
          internal_fn_descriptors_MAP_package_internal_fn] >>
     simp_tac std_ss [EVERY_MAP, EVERY_MEM, FORALL_PROD,
          source_internal_fn_descriptor_def, LET_THM] >>
     rewrite_tac[internal_label_ok_def, internal_fn_label_prefix]) >>
  `MEM (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) packages` by
    (simp[Abbr `packages`, MEM_MAP] >> fs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all entry_runtime_canonical_code >> simp[Abbr `selectors`]
QED

Theorem entry_source_canonical_code:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  valid_vyper_call tops tx cd ret /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ?lbl ce pos mincd pay key ut iv rt
   func se fb label_st dispatch_st checks start cenv registered body_end.
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
         tx.function_name,args,([]:expr list),ret,fbody)) =
      (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) /\
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    func = mk_raw_function "__entry" (all_blocks se) /\
    func.fn_blocks <> [] /\ (HD func.fn_blocks).bb_label = "__entry" /\
    fn_inst_ids_distinct func /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fb,label_st) /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb label_st = ((),dispatch_st) /\ fn_has_code label_st dispatch_st func /\
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce pos 4 start = (cenv,registered) /\
    compile_guarded_body cenv F key ut iv fbody rt registered = ((),body_end) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    dispatch_st.cs_next_var <= checks.cs_next_var /\
    cs_extends start registered /\ cs_extends registered body_end /\
    cs_extends body_end se /\
    fn_has_code checks start func /\ fn_has_code start body_end func /\
    fn_has_code registered body_end func /\
    (!inst. MEM inst (state_insts registered) ==> MEM inst (fn_insts func))
Proof
  strip_tac >>
  `tx.function_name <> "__default__"` by
    fs[e2eDefsTheory.valid_vyper_call_def] >>
  drule supported_entry_no_getters >> strip_tac >>
  `MEM (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
        tx.function_name,args,[],ret,fbody) (FST (classify_functions tops))` by
    (irule external_lookup_raw_package_member >> simp[]) >>
  qspecl_then [`tops`,`rpolicy.rpol_target`,`mut`,
    `lookup_raw_return_or_F (NONE:num option) tx.function_name External tops`,
    `tx.function_name`,`args`,`ret`,`fbody`] strip_assume_tac selected_external_package >>
  `isPREFIX "fn_" ("fn_" ++ tx.function_name) /\
   ~isPREFIX "@" ("fn_" ++ tx.function_name)` by simp[] >>
  drule_all entry_source_canonical_phase >> strip_tac >>
  qexistsl_tac [`"fn_" ++ tx.function_name`,`cenv`,`pos_args`,`min_cds`,
    `is_payable`,`nkey`,`ut`,`iv`,`rt`,`func`,`se`,`fb`,`label_st`,
    `dispatch_st`,`checks`,`start`,`cenv'`,`registered`,`body_end`] >>
  simp[stringTheory.STRCAT_EQNS]
QED

Theorem entry_canonical_checks_reached:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ?lbl ce pos mincd pay key ut iv rt func se checks start cenv registered body_end s.
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
         tx.function_name,args,([]:expr list),ret,fbody)) =
      (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    func = mk_raw_function "__entry" (all_blocks se) /\ fn_inst_ids_distinct func /\
    ~block_is_terminated start /\
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce pos 4 start = (cenv,registered) /\
    compile_guarded_body cenv F key ut iv fbody rt registered = ((),body_end) /\
    cs_extends start registered /\ cs_extends registered body_end /\
    cs_extends body_end se /\
    fn_has_code checks start func /\ fn_has_code start body_end func /\
    fn_has_code registered body_end func /\
    (!inst. MEM inst (state_insts registered) ==> MEM inst (fn_insts func)) /\
    vars_pc_only vs s /\ fresh_vars_wrt checks s /\ ~s.vs_halted /\
    s.vs_current_bb = checks.cs_current_bb /\
    s.vs_inst_idx = LENGTH checks.cs_current_insts /\
    (!fuel r. run_from fuel unit.cu_context func s = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_context fuel' unit.cu_context vs = r)
Proof
  strip_tac >> drule_all entry_source_canonical_code >> strip_tac >>
  `~block_is_terminated checks` by simp[block_is_terminated_def] >>
  drule_all entry_checks_preserve_open >> strip_tac >>
  `lbl = "fn_" ++ tx.function_name` by
    (qpat_assum `set_external_package_target _ _ = _` mp_tac >>
     simp_tac (srw_ss()) [set_external_package_target_def,
       package_external_fn_def, LET_THM] >> metis_tac[]) >>
  drule_all selected_external_dispatch >> strip_tac >>
  `fn_entry_label func = SOME "__entry"` by
    (qpat_x_assum `func = mk_raw_function _ _` kall_tac >>
     simp[fn_entry_label_def, entry_block_def, NULL_EQ]) >>
  `LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_venom_state_calldata_length >> simp[]) >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    fs[initial_venom_state_rel_def] >>
  `EVERY (\(sel,lbl). sel < 2 ** 32)
     (MAP (\(sel,lbl,z). (sel,lbl))
       (build_selectors (type_env tops) (FST (classify_functions tops))))` by
    simp[linear_selectors_lt] >>
  `linear_dispatch_target vs.vs_call_ctx.cc_calldata
     (MAP (\(sel,lbl,z). (sel,lbl))
       (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
     checks.cs_current_bb` by simp[] >>
  drule_all linear_dispatch_context_reaches >> strip_tac >>
  qexistsl_tac [`lbl`,`ce`,`pos`,`mincd`,`pay`,`key`,`ut`,`iv`,`rt`,`func`,
    `se`,`checks`,`start`,`cenv`,`registered`,`body_end`,`s0`] >> gvs[]
QED

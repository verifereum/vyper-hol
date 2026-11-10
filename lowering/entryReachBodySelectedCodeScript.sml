Theory entryReachBodySelectedCode
Ancestors
  externalEntryChecks externalEntryShape actualRegistrationCode
  actualDecoderPackaging loweringShapeDefs loweringShapeProps moduleLowering
  compileEnv compileVyper vyperCompiler venomWf allocaFrontierBound
  fragExec abiDecoderAppend list pair vyperInterpreter e2eDefs

(* Keep all phase witnesses tied to the same occurrence of the package. *)
Theorem entry_selected_phase_equations[local]:
  MEM (lbl,ce,args,mincd,pay,nr,key,ut,iv,fbody,rt) packages /\
  compile_external_fn_bodies packages sd = ((),sx) ==>
  ?checks start cenv registered body_end.
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce args 4 start = (cenv,registered) /\
    compile_guarded_body cenv nr key ut iv fbody rt registered = ((),body_end) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    cs_extends registered body_end /\ cs_extends body_end sx
Proof
  strip_tac >> drule_all external_checks_occurrence >> strip_tac >>
  qpat_x_assum `compile_external_function_body _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_external_function_body_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  `cs_extends cs' sb` by
    metis_tac[compile_guarded_body_labels, pairTheory.SND] >>
  `cs_extends sb sx` by
    (qspecl_then [`post`,`sb`] mp_tac
      compile_external_fn_bodies_label_partition >> simp[]) >>
  qexistsl_tac [`st`,`st'`,`cenv'`,`cs'`,`sb`] >> simp[]
QED

Theorem entry_selected_runtime_phase[local]:
  run_lowering selectors packages internals fallback rpolicy
    buckets metadata dense info "__entry" = SOME unit /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY (\p. isPREFIX "fn_" (FST p)) packages /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internals) /\
  MEM (lbl,ce,args,mincd,pay,nr,key,ut,iv,fbody,rt) packages ==>
  ?func se checks start cenv registered body_end.
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    func.fn_blocks = all_blocks se /\
    MEM func unit.cu_context.ctx_functions /\ fn_inst_ids_distinct func /\
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce args 4 start = (cenv,registered) /\
    compile_guarded_body cenv nr key ut iv fbody rt registered = ((),body_end) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    cs_extends registered body_end /\ cs_extends body_end se /\
    fn_has_code registered body_end func /\
    (!inst. MEM inst (state_insts registered) ==> MEM inst (fn_insts func))
Proof
  strip_tac >> drule_all run_lowering_entry_function_labels >> strip_tac >>
  `EVERY (\(sel,lbl). jump_label_ok lbl)
     (MAP (\(sel,lbl,z). (sel,lbl)) selectors)` by
    (gvs[EVERY_MAP, EVERY_MEM, pairTheory.FORALL_PROD,
         loweringShapeDefsTheory.jump_label_ok_def] >> metis_tac[]) >>
  drule_all runtime_entry_dispatch_code_labels >> strip_tac >>
  drule_all entry_selected_phase_equations >> strip_tac >>
  `cs_extends body_end se` by metis_tac[cs_extends_trans] >>
  `MEM func unit.cu_context.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  `fn_inst_ids_distinct func` by
    (drule run_lowering_static_integrity >> strip_tac >>
     qpat_x_assum `MEM func _` (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
     gvs[ctx_inst_ids_distinct_def, fn_inst_ids_distinct_def,
         MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks se))` by
    (drule run_lowering_context_ok >>
     simp[lowering_context_ok_def, EVERY_MEM] >> strip_tac >>
     qpat_x_assum `!fn. MEM fn _ ==> ALL_DISTINCT _ /\ _`
       (qspec_then `func` mp_tac) >>
     simp[venomInstTheory.fn_labels_def]) >>
  `fn_has_code registered body_end func` by
    (`cs_extends registered registered` by simp[cs_extends_refl] >>
     drule_all external_decoder_fn_has_code >>
     simp[fn_has_code_def, venomInstTheory.mk_raw_function_def]) >>
  qexistsl_tac [`func`,`se`,`checks`,`start`,`cenv`,`registered`,`body_end`] >>
  simp[] >> gen_tac >> strip_tac >>
  `cs_extends registered se` by metis_tac[cs_extends_trans] >>
  `abi_decoder_code_member inst registered` by
    simp[decoder_code_member_state_insts] >>
  drule_all external_phase_decoder_owned >>
  simp[venomInstTheory.fn_insts_def, venomInstTheory.mk_raw_function_def]
QED

Theorem entry_selected_source_phase[local]:
  !tops rpolicy unit mut nr rr name args dflts ret fbody
   lbl ce pos_args mincd pay nr' key ut iv rt.
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  MEM (mut,nr,rr,name,args,dflts,ret,fbody) (FST (classify_functions tops)) /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops F (assign_nkeys tops 0)
      (mut,nr,rr,name,args,dflts,ret,fbody)) =
    (lbl,ce,pos_args,mincd,pay,nr',key,ut,iv,fbody,rt) ==>
  ?func se checks start cenv registered body_end.
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    func.fn_blocks = all_blocks se /\
    MEM func unit.cu_context.ctx_functions /\ fn_inst_ids_distinct func /\
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce pos_args 4 start = (cenv,registered) /\
    compile_guarded_body cenv nr' key ut iv fbody rt registered = ((),body_end) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    cs_extends registered body_end /\ cs_extends body_end se /\
    fn_has_code registered body_end func /\
    (!inst. MEM inst (state_insts registered) ==> MEM inst (fn_insts func))
Proof
  rpt gen_tac >> strip_tac >>
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
    (simp[Abbr `packages`, EVERY_MAP, EVERY_MEM, FORALL_PROD,
          set_external_package_target_def, package_external_fn_def, LET_THM]) >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns)` by
    (simp_tac std_ss [Abbr `internal_fns`, GSYM MAP_MAP_o,
          internal_fn_descriptors_set_internal_package_target,
          internal_fn_descriptors_MAP_package_internal_fn] >>
     simp_tac std_ss [EVERY_MAP, EVERY_MEM, FORALL_PROD,
          source_internal_fn_descriptor_def, LET_THM] >>
     rewrite_tac[loweringShapeDefsTheory.internal_label_ok_def,
                 internal_fn_label_prefix]) >>
  `MEM (lbl,ce,pos_args,mincd,pay,nr',key,ut,iv,fbody,rt) packages` by
    (simp[Abbr `packages`, MEM_MAP] >> fs[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule_all entry_selected_runtime_phase >> simp[]
QED

Theorem entry_selected_classified_raw[local]:
  !ts name mut nr args dflts ret fbody.
  lookup_function (NONE:num option) name External ts =
    SOME (mut,nr,args,dflts,ret,fbody) /\ name <> "__default__" /\
  (!nr' mut' typ x. ~MEM (VariableDecl (Public nr') mut' name typ x) ts) /\
  (!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b name kt vt x) ts) ==>
  MEM (mut,nr,lookup_raw_return_or_F (NONE:num option) name External ts,
       name,args,dflts,ret,fbody) (FST (classify_functions ts))
Proof
  Induct >- simp[lookup_function_def] >>
  rpt gen_tac >> Cases_on `classify_functions ts` >> PairCases_on `r` >>
  Cases_on `h`
  >- (rename1 `FunctionDecl vis fm nk rr fname fa fd fr fb` >>
      Cases_on `vis` >> Cases_on `fname = name` >>
      Cases_on `fname = "__default__"` >>
      gvs[lookup_function_def, lookup_raw_return_or_F_def, lookup_raw_return_def,
          classify_functions_def, classify_function_def] >> metis_tac[])
  >- (rename1 `VariableDecl vis vm vname vt vx` >> Cases_on `vis` >>
      gvs[lookup_function_def, lookup_raw_return_or_F_def, lookup_raw_return_def,
          classify_functions_def, classify_function_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[])
  >- (rename1 `HashMapDecl vis hb hname kt vt hx` >> Cases_on `vis` >>
      gvs[lookup_function_def, lookup_raw_return_or_F_def, lookup_raw_return_def,
          classify_functions_def, classify_function_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  gvs[lookup_function_def, lookup_raw_return_or_F_def, lookup_raw_return_def,
      classify_functions_def, classify_function_def] >> metis_tac[]
QED

Theorem entry_selected_source_code:
  !tops rpolicy unit tx cd ret mut args fbody.
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  valid_vyper_call tops tx cd ret /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  ?lbl ce pos_args mincd pay key ut iv rt
   func se checks start cenv registered body_end.
    set_external_package_target rpolicy.rpol_target
      (package_external_fn tops F (assign_nkeys tops 0)
        (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
         tx.function_name,args,([] : expr list),ret,fbody)) =
      (lbl,ce,pos_args,mincd,pay,F,key,ut,iv,fbody,rt) /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    func.fn_blocks = all_blocks se /\
    MEM func unit.cu_context.ctx_functions /\ fn_inst_ids_distinct func /\
    compile_entry_checks mincd pay checks = ((),start) /\
    compile_register_positional_args ce pos_args 4 start = (cenv,registered) /\
    compile_guarded_body cenv F key ut iv fbody rt registered = ((),body_end) /\
    checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
    cs_extends registered body_end /\ cs_extends body_end se /\
    fn_has_code registered body_end func /\
    (!inst. MEM inst (state_insts registered) ==> MEM inst (fn_insts func))
Proof
  rpt gen_tac >> strip_tac >>
  drule supported_entry_no_getters >> strip_tac >>
  `tx.function_name <> "__default__"` by fs[valid_vyper_call_def] >>
  `MEM (mut,F,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
        tx.function_name,args,[],ret,fbody) (FST (classify_functions tops))` by
    (irule entry_selected_classified_raw >> simp[]) >>
  qspecl_then [`tops`,`rpolicy.rpol_target`,`mut`,
    `lookup_raw_return_or_F (NONE:num option) tx.function_name External tops`,
    `tx.function_name`,`args`,`ret`,`fbody`] strip_assume_tac selected_external_package >>
  drule_all entry_selected_source_phase >> strip_tac >>
  qexistsl_tac [`"fn_" ++ tx.function_name`,`cenv`,`pos_args`,`min_cds`,
    `is_payable`,`nkey`,`ut`,`iv`,`rt`,`func`,`se`,`checks`,`start`,
    `cenv'`,`registered`,`body_end`] >> gvs[stringTheory.STRCAT_EQNS] >>
  first_assum ACCEPT_TAC
QED

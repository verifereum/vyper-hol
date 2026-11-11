(* Source classification probes for entry ownership. *)
Theory sourceEntryCode
Ancestors supportedProgramProps entryDispatchProps compileVyper
  rawEntryCode entryCheckIntervals sourceEntrySelection supportedProgram supportedDecls
  loweringShapeSource loweringShapeProps loweringShapeDefs compileEnv supportedNames list
  vyperCompiler actualDecoderPackaging actualRegistrationCode moduleLowering

Theorem supported_fallback_not_external_table:
  supported_program
    [FunctionDecl External Payable F F "__default__" [] [] NoneT [Pass]] /\
  vyperInterpreter$lookup_function NONE "__default__" External
    [FunctionDecl External Payable F F "__default__" [] [] NoneT [Pass]] =
    SOME (Payable,F,[],[],NoneT,[Pass]) /\
  FST (classify_functions
    [FunctionDecl External Payable F F "__default__" [] [] NoneT [Pass]]) = []
Proof
  EVAL_TAC
QED

Theorem supported_external_lookup_member:
  supported_program tops /\ name <> "__default__" /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) ==>
  ?rr. MEM (mut,nr,rr,name,args,dflts,ret,fbody)
    (FST (classify_functions tops))
Proof
  strip_tac >>
  `!nr' mut' typ x. ~MEM (VariableDecl (Public nr') mut' name typ x) tops` by
    (rpt strip_tac >> drule_all supported_program_declaration >>
     simp[supported_declaration_header_def]) >>
  `!nr' b kt vt x. ~MEM (HashMapDecl (Public nr') b name kt vt x) tops` by
    (rpt strip_tac >> drule_all supported_program_declaration >>
     simp[supported_declaration_header_def]) >>
  drule_all lookup_function_external_mem >> simp[]
QED

Theorem source_runtime_entry_witness:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ name <> "__default__" /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?sels extpkgs fallback label_st dispatch_st external_st entry_end
    cenv pos_args min_cds nkey transient view ret_type.
    sels = build_selectors (type_env tops) (FST (classify_functions tops)) /\
    MEM ("fn_" ++ name,cenv,pos_args,min_cds,mut = Payable,F,nkey,
      transient,view,fbody,ret_type) extpkgs /\
    EVERY external_fn_shape_ok extpkgs /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback,label_st) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fallback label_st = ((),dispatch_st) /\
    compile_external_fn_bodies extpkgs dispatch_st = ((),external_st) /\
    shape_state dispatch_st /\
    cs_extends label_st dispatch_st /\
    cs_extends dispatch_st external_st /\ cs_extends external_st entry_end /\
    efn = mk_raw_function "__entry" (all_blocks entry_end) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks entry_end)) /\
    fn_has_code label_st dispatch_st efn /\ fn_has_code dispatch_st external_st efn
Proof
  strip_tac >>
  drule_all supported_external_lookup_member >> strip_tac >>
  `runtime_bodies_shape_ok tops` by
    metis_tac[supported_program_runtime_bodies_shape_ok] >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
    (FST (SND (classify_functions tops))))` by
    (irule supported_names_internal_names_distinct >>
     fs[supported_program_def, supported_declaration_names_def]) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, bool_case_eq] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor)` >>
  simp[] >> strip_tac >>
  `~EXISTS external_has_defaults exts` by
    (drule supported_program_no_external_defaults >> simp[]) >>
  qpat_x_assum `(if EXISTS external_has_defaults exts then _ else _) = _`
    mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  qspecl_then [`tops`, `F`] mp_tac internal_descriptors_ok >>
  impl_tac >- fs[] >>
  rewrite_tac[pairTheory.FST, pairTheory.SND] >> strip_tac >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl)
    (build_selectors (type_env tops) exts)` by
    rewrite_tac[build_selectors_fn_labels] >>
  `EVERY external_fn_shape_ok
    (MAP (set_external_package_target rpolicy.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot)) exts)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_external_fn_shape_ok >> gs[]) >>
  `EVERY internal_fn_shape_ok
    (MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops T (K global_nonreentrant_slot) F 0) ints)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_internal_fn_shape_ok >> gs[]) >>
  `fallback_shape_ok (set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn tops T (K global_nonreentrant_slot) fb))` by
    (qspecl_then [`tops`, `T`, `K global_nonreentrant_slot`,
       `rpolicy.rpol_target`] mp_tac package_fallback_fn_shape_ok >> gs[]) >>
  gvs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
    internal_fn_descriptors_MAP_package_internal_fn] >>
  qmatch_asmsub_abbrev_tac `run_lowering sels extpkgs intpkgs fbpkg` >>
  `lowering_policy_ok rpolicy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  Cases_on `compile_generate_runtime sels extpkgs intpkgs fbpkg Linear 0 0 []
    (build_dense_entry_info sels extpkgs) (initial_compile_state "__entry")` >>
  rename1 `_ = (u,final)` >> Cases_on `u` >>
  drule runtime_external_boundary >>
  impl_tac >- simp[shape_state_initial_compile_state] >> strip_tac >>
  `EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors intpkgs) /\
   ALL_DISTINCT (MAP FST (internal_fn_descriptors intpkgs))` by
    simp[Abbr `intpkgs`, internal_fn_descriptors_set_internal_package_target,
      internal_fn_descriptors_MAP_package_internal_fn] >>
  `MEM (mk_raw_function "__entry" (all_blocks entry_end))
    unit.cu_context.ctx_functions` by
    (drule run_lowering_packaged_entry_member >>
     disch_then (qspecl_then [`r`, `final`, `entry_end`] mp_tac) >> simp[]) >>
  `shape_state (initial_compile_state "__entry")` by
    simp[shape_state_initial_compile_state] >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels` by
    simp[Abbr `sels`, build_selectors_fn_labels] >>
  drule_all runtime_dispatch_shape_boundary >> strip_tac >>
  drule_all external_bodies_run_shape >> strip_tac >>
  drule_all external_fallback_suffix_extends >> strip_tac >>
  `cs_extends label_st dispatch_st` by
    (qpat_x_assum `fresh_label _ _ = _` mp_tac >>
     simp[fresh_label_def] >> strip_tac >> gvs[] >>
     fs[cs_extends_def]) >>
  `cs_extends dispatch_st entry_end` by metis_tac[cs_extends_trans] >>
  drule_all run_lowering_entry_interval >> strip_tac >>
  `fn_has_code label_st dispatch_st efn` by
    (gvs[] >> irule external_decoder_fn_has_code >>
     simp[] >> qexists_tac `label_st` >> simp[cs_extends_refl]) >>
  qexistsl_tac [`extpkgs`, `fallback_lbl`, `label_st`,
    `dispatch_st`, `external_st`, `entry_end`] >> simp[Abbr `sels`] >>
  `MEM (set_external_package_target rpolicy.rpol_target
      (package_external_fn tops T (K global_nonreentrant_slot)
        (mut,F,rr,name,args,([] : expr list),ret,fbody))) extpkgs` by
    (simp_tac pure_ss [Abbr `extpkgs`, MEM_MAP] >>
     qexists_tac `package_external_fn tops T (K global_nonreentrant_slot)
       (mut,F,rr,name,args,([] : expr list),ret,fbody)` >>
     conj_tac >- REFL_TAC >>
     qexists_tac `(mut,F,rr,name,args,([] : expr list),ret,fbody)` >>
     conj_tac >- REFL_TAC >> first_assum ACCEPT_TAC) >>
  pop_assum mp_tac >>
  simp[package_external_fn_def, set_external_package_target_def] >>
  metis_tac[]
QED

Theorem source_selected_entry_check_code:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ name <> "__default__" /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?fb ds de opened checked min_cds.
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb ds = ((),de) /\
    fn_has_code ds de efn /\
    ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\
    ds.cs_next_var = 0 /\
    compile_entry_checks min_cds (mut = Payable) opened = ((),checked) /\
    fn_has_code opened checked efn /\
    opened.cs_current_bb = "fn_" ++ name /\
    opened.cs_current_insts = [] /\ ~block_is_terminated opened
Proof
  strip_tac >> drule_all source_runtime_entry_witness >> strip_tac >>
  drule_all installed_selected_check_code >> strip_tac >>
  `label_st.cs_blocks = [] /\ label_st.cs_current_insts = [] /\
   label_st.cs_next_var = 0 /\
   label_st.cs_current_bb = (initial_compile_state "__entry").cs_current_bb` by
    (qpat_x_assum `fresh_label _ _ = _` mp_tac >>
     simp[fresh_label_def, initial_compile_state_def] >>
     strip_tac >> gvs[]) >>
  `cs_extends label_st entry_end` by metis_tac[cs_extends_trans] >>
  drule_all cs_extends_raw_entry_label >>
  disch_then (qspec_then `"__entry"` mp_tac) >>
  gvs[] >> strip_tac >>
  qexistsl_tac [`fallback`, `label_st`, `dispatch_st`, `opened`, `checked`, `min_cds`] >>
  simp[]
QED

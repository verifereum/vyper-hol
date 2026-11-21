(* Installed intervals for the ordinary runtime dispatcher's default entry. *)
Theory defaultDispatchPlacement
Ancestors entryRejectCode selectedEntryPrefixCode runtimeBodyStartDefs entryCheckIntervals
  externalEntryChecks supportedNames moduleLowering compileVyper
  compileEnv vyperCompiler supportedProgram list
  runtimeExternalPackageCode loweringShapeSource loweringShapeProps loweringShapeDefs
  vyperTypeContractSoundness fragExec entryLinearAppend
  entryCompileIntervals

Theorem default_runtime_compile_layout:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ raw_shape_free_program tops /\
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?sels extpkgs fbpkg fallback label_st dispatch_st external_st checks entry_end.
    sels = build_selectors (type_env tops) (FST (classify_functions tops)) /\
    extpkgs = MAP (set_external_package_target rpolicy.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot))
      (FST (classify_functions tops)) /\
    fbpkg = set_fallback_package_target rpolicy.rpol_target
      (package_fallback_fn tops T (K global_nonreentrant_slot)
        (FST (SND (SND (classify_functions tops))))) /\
    EVERY external_fn_shape_ok extpkgs /\
    fallback_shape_ok fbpkg /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback,label_st) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fallback label_st = ((),dispatch_st) /\
    compile_external_fn_bodies extpkgs dispatch_st = ((),external_st) /\
    new_block fallback external_st = (external_st.cs_current_bb,checks) /\
    (case fbpkg of NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
      | SOME (ce,pay,nr,key,ut,iv,fbody,rt) =>
          compile_fallback_body ce pay nr key ut iv fbody rt) checks = ((),entry_end) /\
    shape_state label_st /\ shape_state dispatch_st /\
    shape_state external_st /\ shape_state checks /\ shape_state entry_end /\
    cs_extends label_st dispatch_st /\
    cs_extends dispatch_st external_st /\ cs_extends external_st checks /\
    cs_extends checks entry_end /\
    efn = mk_raw_function "__entry" (all_blocks entry_end) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks entry_end)) /\
    fn_has_code label_st dispatch_st efn /\
    fn_has_code dispatch_st external_st efn /\ fn_has_code checks entry_end efn /\
    label_st.cs_current_bb = elbl /\ label_st.cs_current_insts = [] /\
    label_st.cs_next_var = 0
Proof
  ACCEPT_TAC runtime_linear_compile_layout_static
QED

Theorem default_fallback_compile_placement:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME elbl /\
  set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn tops T (K global_nonreentrant_slot)
      (FST (SND (SND (classify_functions tops))))) =
    SOME (ce,pay,nr,key,ut,iv,fbody,rt) ==>
  ?fallback label_st dispatch_st opened checks st st'.
    runtime_fallback_body_start tops rpolicy
      (lbl,ce,[],4,pay,nr,key,ut,iv,fbody,rt) st /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback,label_st) /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fallback label_st = ((),dispatch_st) /\
    compile_external_fn_bodies
      (MAP (set_external_package_target rpolicy.rpol_target o
        package_external_fn tops T (K global_nonreentrant_slot))
        (FST (classify_functions tops))) dispatch_st = ((),opened) /\
    new_block fallback opened = (opened.cs_current_bb,checks) /\
    compile_entry_checks 4 pay checks = ((),st) /\
    compile_register_positional_args ce [] 4 st = (ce,st) /\
    compile_guarded_body ce nr key ut iv fbody rt st = ((),st') /\
    cs_extends label_st dispatch_st /\ cs_extends dispatch_st checks /\
    cs_extends checks st /\ cs_extends st st' /\
    fn_has_code label_st dispatch_st func /\ fn_has_code checks st func /\
    fn_has_code st st func /\ fn_has_code st st' func /\ ~block_is_terminated st /\
    label_st.cs_current_bb = "__entry" /\ label_st.cs_current_bb = elbl /\
    label_st.cs_current_insts = [] /\ label_st.cs_next_var = 0
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor)` >> fs[] >>
  `~EXISTS external_has_defaults exts` by fs[] >>
  drule_all lower_vyper_runtime_legacy_packages >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  `elbl = "__entry"` by
    (drule_all lower_vyper_runtime_unit_entry_label >> simp[]) >>
  qpat_assum `set_fallback_package_target _ _ = SOME _` (fn th =>
    qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _`
      (assume_tac o REWRITE_RULE [th])) >>
  drule_all run_lowering_fallback_interval_code >> strip_tac >>
  `~block_is_terminated st` by
    (irule compile_entry_checks_open >>
     qexistsl [`4`, `pay`, `checks`, `()`] >> simp[block_is_terminated_def]) >>
  `fn_has_code st st func` by
    (qspecl_then [`st`, `st`, `se`, `func`] mp_tac fn_has_code_split >>
     simp[cs_extends_refl]) >>
  qexistsl [`fl`, `sf`, `sd`, `opened`, `checks`, `st`, `se`] >>
  simp[compile_register_positional_args_def, comp_return_def] >>
  Cases_on `fb` >- fs[package_fallback_fn_def, set_fallback_package_target_def] >>
  simp[runtime_fallback_body_start_def] >>
  qexistsl [`x`, `fl`, `sf`, `sd`, `opened`, `checks`] >> fs[]
QED

Theorem default_selected_compile_placement:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME elbl /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  MEM (mut,F,rr,name,args,[],ret,fbody) (FST (classify_functions tops)) /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,F,rr,name,args,([]:expr list),ret,fbody)) =
    (lbl,ce,pargs,mincd,pay,F,key,ut,iv,fbody,rt) ==>
  ?pre post fallback label_st dispatch_st before checks st ce' body_st st'.
    runtime_selected_body_start tops rpolicy
      (lbl,ce,pargs,mincd,pay,F,key,ut,iv,fbody,rt) st /\
    MAP (set_external_package_target rpolicy.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot))
      (FST (classify_functions tops)) =
      pre ++ (lbl,ce,pargs,mincd,pay,F,key,ut,iv,fbody,rt)::post /\
    ~MEM lbl (MAP FST pre) /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback,label_st) /\
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fallback label_st = ((),dispatch_st) /\
    compile_external_fn_bodies pre dispatch_st = ((),before) /\
    new_block lbl before = (before.cs_current_bb,checks) /\
    compile_entry_checks mincd pay checks = ((),st) /\
    compile_register_positional_args ce pargs 4 st = (ce',body_st) /\
    compile_guarded_body ce' F key ut iv fbody rt body_st = ((),st') /\
    cs_extends label_st dispatch_st /\ cs_extends dispatch_st checks /\
    cs_extends checks st /\ cs_extends st body_st /\ cs_extends body_st st' /\
    fn_has_code label_st dispatch_st func /\ fn_has_code checks st func /\
    fn_has_code st body_st func /\ fn_has_code body_st st' func /\
    label_st.cs_current_bb = elbl /\ label_st.cs_current_insts = [] /\
    label_st.cs_next_var = 0
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  rename1 `classify_functions tops = (exts,ints,fb,ctor)` >> fs[] >>
  `~EXISTS external_has_defaults exts` by fs[] >>
  drule_all lower_vyper_runtime_legacy_packages >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `extpkgs = MAP (set_external_package_target rpolicy.rpol_target o
    package_external_fn tops T (K global_nonreentrant_slot)) exts` >>
  `MEM (lbl,ce,pargs,mincd,pay,F,key,ut,iv,fbody,rt) extpkgs` by
    (simp[Abbr `extpkgs`, MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all run_lowering_selected_entry_code >> strip_tac >>
  `ALL_DISTINCT (MAP FST extpkgs)` by
    (drule externalEntryChecksTheory.classified_external_labels_distinct >>
     fs[Abbr `extpkgs`, MAP_MAP_o, combinTheory.o_DEF, pairTheory.LAMBDA_PROD,
        package_external_fn_def, set_external_package_target_def]) >>
  `~MEM lbl (MAP FST pre)` by (gvs[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `runtime_selected_body_start tops rpolicy
     (lbl,ce,pargs,mincd,pay,F,key,ut,iv,fbody,rt) sk` by
    (simp[runtime_selected_body_start_def] >>
     qexistsl_tac [`pre`, `post`, `before`, `sc`] >> fs[Abbr `extpkgs`]) >>
  `elbl = "__entry"` by
    (drule_all lower_vyper_runtime_unit_entry_label >> simp[]) >>
  qexistsl [`pre`, `post`, `fl`, `sf`, `sd`, `before`, `sc`, `sk`, `cenv`, `sa`, `sb`] >>
  simp[] >> rpt conj_tac
  >- (drule (SRULE [cs_appends_def] cs_appends_selector_dispatch_linear) >> simp[])
  >- (drule (SRULE [cs_appends_def] cs_appends_guarded_body) >> simp[])
QED

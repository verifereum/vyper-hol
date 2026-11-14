(* Compiler layout for arbitrary-calldata entry placement. *)
Theory defaultDispatchPlacement
Ancestors runtimeExternalPackageCode runtimeBodyStartDefs entryRuntimePrefix
  supportedProgramProps entryDispatchProps compileVyper
  classifiedExternalLabels pair rawEntryCode entryCheckIntervals sourceEntrySelection supportedProgram supportedDecls
  loweringShapeSource loweringShapeRules loweringShapeProps loweringShapeDefs compileEnv supportedNames list
  vyperCompiler actualDecoderPackaging actualRegistrationCode moduleLowering

Theorem default_runtime_compile_layout:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
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
  strip_tac >>
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
  qpat_x_assum `(if EXISTS external_has_defaults exts then _ else _) = _` mp_tac >>
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
     simp[fresh_label_def] >> strip_tac >> gvs[] >> fs[cs_extends_def]) >>
  `cs_extends dispatch_st entry_end` by metis_tac[cs_extends_trans] >>
  drule_all run_lowering_entry_interval >> strip_tac >>
  `fn_has_code label_st dispatch_st efn` by
    (gvs[] >> irule external_decoder_fn_has_code >>
     simp[] >> qexists_tac `label_st` >> simp[cs_extends_refl]) >>
  `shape_state label_st` by
    (`shape_step F jump_label_ok (\st. T) (fresh_label "fallback")
       (\l st. T /\ compiler_label l)` by
       (ho_match_mp_tac shape_step_fresh_label >> simp[shape_stable_def]) >>
     pop_assum mp_tac >> simp[shape_step_def] >>
     disch_then drule >> simp[] >> strip_tac >> gvs[]) >>
  `label_st.cs_blocks = [] /\ label_st.cs_current_insts = [] /\
   label_st.cs_next_var = 0 /\
   label_st.cs_current_bb = (initial_compile_state "__entry").cs_current_bb` by
    (qpat_x_assum `fresh_label _ _ = _` mp_tac >>
     simp[fresh_label_def] >> strip_tac >> gvs[] >>
     simp[initial_compile_state_def, shape_state_def]) >>
  `cs_extends label_st entry_end` by metis_tac[cs_extends_trans] >>
  drule_all cs_extends_raw_entry_label >>
  disch_then (qspec_then `"__entry"` mp_tac) >> gvs[] >> strip_tac >>
  `shape_state fallback_st` by metis_tac[shape_state_new_block] >>
  `cs_extends external_st fallback_st` by metis_tac[cs_extends_new_block] >>
  drule runtime_fallback_shape >> simp[shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  `cs_extends fallback_st entry_end` by fs[shape_extends_def] >>
  `fn_has_code fallback_st entry_end
    (mk_raw_function "__entry" (all_blocks entry_end))` by
    (irule external_decoder_fn_has_code >> simp[cs_extends_refl] >>
     qexists `fallback_st` >> simp[cs_extends_refl]) >>
  qexistsl [`fallback_lbl`, `label_st`, `dispatch_st`, `external_st`,
    `fallback_st`, `entry_end`] >>
  simp[Abbr `sels`, Abbr `extpkgs`, Abbr `fbpkg`]
QED

Theorem default_fallback_compile_placement:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME elbl /\
  FST (SND (SND (classify_functions tops))) =
    SOME (mut,F,rr,"__default__",[],[],ret,fbody) /\
  set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn tops T (K global_nonreentrant_slot)
      (FST (SND (SND (classify_functions tops))))) =
    SOME (ce,pay,F,key,ut,iv,fbody,rt) ==>
  ?fallback label_st dispatch_st opened checks st st'.
    runtime_fallback_body_start tops rpolicy
      (lbl,ce,[],4,pay,F,key,ut,iv,fbody,rt) st /\
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
    compile_guarded_body ce F key ut iv fbody rt st = ((),st') /\
    shape_state label_st /\ shape_state dispatch_st /\ shape_state opened /\
    shape_state checks /\ shape_state st /\ shape_state st' /\
    cs_extends label_st dispatch_st /\ cs_extends dispatch_st opened /\
    cs_extends opened checks /\ cs_extends checks st /\ cs_extends st st' /\
    fn_has_code label_st dispatch_st func /\ fn_has_code checks st func /\
    fn_has_code st st func /\ fn_has_code st st' func /\
    label_st.cs_current_bb = elbl /\ label_st.cs_current_insts = [] /\
    label_st.cs_next_var = 0
Proof
  strip_tac >> drule_all default_runtime_compile_layout >> strip_tac >> gvs[] >> fs[] >>
  qpat_x_assum `compile_fallback_body _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  `compile_fallback_body ce pay F key ut iv fbody rt =
   comp_ignore_bind (compile_entry_checks 4 pay)
     (compile_guarded_body ce F key ut iv fbody rt)` by
    (simp[compile_fallback_body_def, compile_entry_checks_def,
      comp_ignore_bind_def, comp_bind_def, comp_return_def, FUN_EQ_THM] >>
     gen_tac >> pairarg_tac >> simp[]) >>
  pop_assum SUBST1_TAC >>
  simp[comp_ignore_bind_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_entry_checks 4 pay checks = (u,st)` >> Cases_on `u` >>
  mp_tac compile_entry_checks_shape >> simp[shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  `cs_extends checks st` by fs[shape_extends_def] >>
  `cenv_shape_ok st ce` by
    (irule cenv_static_ok_shape_ok >> fs[fallback_shape_ok_def]) >>
  `ce.ce_return_pc = NONE /\
   ~supported_stmts_expr_exists expr_shape_root fbody` by
    fs[fallback_shape_ok_def] >>
  drule compile_guarded_body_env_shape >> simp[] >>
  rewrite_tac[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  `cs_extends st entry_end` by fs[shape_extends_def] >>
  qexistsl [`fallback`, `label_st`, `dispatch_st`, `external_st`, `checks`,
    `st`, `entry_end`] >>
  simp[compile_register_positional_args_def, comp_return_def] >>
  conj_tac
  >- (rw[runtime_fallback_body_start_def] >>
      Cases_on `classify_functions tops` >> PairCases_on `r` >> gvs[] >>
      qexistsl [`fallback`, `label_st`, `dispatch_st`, `external_st`, `checks`] >> simp[]) >>
  rpt conj_tac >> irule external_decoder_fn_has_code >>
  simp[cs_extends_refl] >> qexists `checks` >> simp[cs_extends_refl]
QED

Theorem default_selected_compile_placement:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
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
    shape_state label_st /\ shape_state dispatch_st /\ shape_state checks /\
    shape_state st /\ shape_state body_st /\ shape_state st' /\
    cs_extends label_st dispatch_st /\ cs_extends dispatch_st checks /\
    cs_extends checks st /\ cs_extends st body_st /\ cs_extends body_st st' /\
    fn_has_code label_st dispatch_st func /\ fn_has_code checks st func /\
    fn_has_code st body_st func /\ fn_has_code body_st st' func /\
    label_st.cs_current_bb = elbl /\ label_st.cs_current_insts = [] /\
    label_st.cs_next_var = 0
Proof
  strip_tac >> drule_all default_runtime_compile_layout >> strip_tac >>
  `MEM (lbl,ce,pargs,mincd,pay,F,key,ut,iv,fbody,rt) extpkgs` by
    (gvs[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
  `ALL_DISTINCT (MAP FST extpkgs)` by
    (gvs[] >> drule classifiedExternalLabelsTheory.classified_external_labels_distinct >>
     simp[MAP_MAP_o, combinTheory.o_DEF, LAMBDA_PROD,
       package_external_fn_def, set_external_package_target_def]) >>
  drule_all compile_external_member_interval >> strip_tac >>
  `~MEM lbl (MAP FST pre)` by (gvs[MAP_APPEND, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  qpat_x_assum `extpkgs = pre ++ _` SUBST_ALL_TAC >>
  drule_all external_selected_check_interval >> strip_tac >>
  gvs[] >>
  `cenv_shape_ok checked ce` by
    (irule cenv_static_ok_shape_ok >> fs[external_fn_shape_ok_def]) >>
  qspecl_then [`pargs`, `ce`, `4`] mp_tac compile_register_positional_args_shape >>
  rewrite_tac[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  `cs_extends checked sa` by fs[shape_extends_def] >>
  `ce'.ce_return_pc = NONE /\
   ~supported_stmts_expr_exists expr_shape_root fbody` by
    fs[external_fn_shape_ok_def] >>
  drule compile_guarded_body_env_shape >> simp[] >>
  rewrite_tac[shape_step_def] >> disch_then drule >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexistsl [`pre`, `post`, `fallback`, `label_st`, `dispatch_st`, `before`,
    `opened`, `checked`, `ce'`, `sa`, `se`] >> simp[] >>
  conj_tac
  >- (rw[runtime_selected_body_start_def] >>
      Cases_on `classify_functions tops` >> PairCases_on `r` >> gvs[] >>
      qexistsl [`pre`, `post`, `fallback`, `label_st`, `dispatch_st`, `before`,
        `opened`] >> simp[]) >>
  rpt conj_tac >> irule external_decoder_fn_has_code >>
  simp[cs_extends_refl] >> metis_tac[cs_extends_trans, cs_extends_refl]
QED

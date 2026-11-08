(* The installed raw entry and its exact external package list. *)
Theory runtimeExternalPackageCode
Ancestors supportedProgramProps entryDispatchProps compileVyper
  rawEntryCode entryCheckIntervals sourceEntrySelection supportedProgram supportedDecls
  loweringShapeSource loweringShapeRules loweringShapeProps loweringShapeDefs compileEnv supportedNames list
  vyperCompiler actualDecoderPackaging actualRegistrationCode moduleLowering

Theorem source_runtime_external_packages:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?sels extpkgs fallback label_st dispatch_st external_st entry_end.
    sels = build_selectors (type_env tops) (FST (classify_functions tops)) /\
    extpkgs = MAP (set_external_package_target rpolicy.rpol_target o
      package_external_fn tops F (assign_nkeys tops 0))
      (FST (classify_functions tops)) /\
    EVERY external_fn_shape_ok extpkgs /\
    fresh_label "fallback" (initial_compile_state "__entry") = (fallback,label_st) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
      fallback label_st = ((),dispatch_st) /\
    compile_external_fn_bodies extpkgs dispatch_st = ((),external_st) /\
    shape_state label_st /\ shape_state dispatch_st /\
    cs_extends label_st dispatch_st /\
    cs_extends dispatch_st external_st /\ cs_extends external_st entry_end /\
    efn = mk_raw_function "__entry" (all_blocks entry_end) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks entry_end)) /\
    fn_has_code label_st dispatch_st efn /\ fn_has_code dispatch_st external_st efn /\
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
  qspecl_then [`tops`, `F`] mp_tac internal_descriptors_ok >>
  impl_tac >- fs[] >>
  rewrite_tac[pairTheory.FST, pairTheory.SND] >> strip_tac >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl)
    (build_selectors (type_env tops) exts)` by
    rewrite_tac[build_selectors_fn_labels] >>
  `EVERY external_fn_shape_ok
    (MAP (set_external_package_target rpolicy.rpol_target o
      package_external_fn tops F (assign_nkeys tops 0)) exts)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_external_fn_shape_ok >> gs[]) >>
  `EVERY internal_fn_shape_ok
    (MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops F (assign_nkeys tops 0) F 0) ints)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_internal_fn_shape_ok >> gs[]) >>
  `fallback_shape_ok (set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn tops F (assign_nkeys tops 0) fb))` by
    (qspecl_then [`tops`, `F`, `assign_nkeys tops 0`,
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
  qexistsl_tac [`fallback_lbl`, `label_st`,
    `dispatch_st`, `external_st`, `entry_end`] >>
  simp[Abbr `sels`, Abbr `extpkgs`]
QED

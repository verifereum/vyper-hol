(* Install the rejecting prefix from the classified fallback package. *)
Theory dispatchedValueFallback
Ancestors runtimeExternalPackageCode sourceEntryCode entryRuntimePrefix
  actualDecoderPackaging actualRegistrationCode rawEntryCode entryCheckIntervals
  supportedProgramProps loweringShapeSource loweringShapeRules loweringShapeProps
  loweringShapeDefs compileVyper moduleLowering compileEnv fragExec list
  supportedProgram supportedDecls supportedNames vyperCompiler

Theorem classified_fallback_runtime_interval[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  FST (SND (SND (classify_functions tops))) =
    SOME (mut,F,rr,"__default__",args,[],ret,fbody) /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?fb ds de sx opened entry_end ce key tr view rt.
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb ds = ((),de) /\
    fn_has_code ds de efn /\
    ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\ ds.cs_next_var = 0 /\
    new_block fb sx = (sx.cs_current_bb,opened) /\
    compile_fallback_body ce (mut = Payable) F key tr view fbody rt opened =
      ((),entry_end) /\
    cenv_static_ok ce /\ ce.ce_return_pc = NONE /\
    ~supported_stmts_expr_exists expr_shape_root fbody /\
    shape_state opened /\ fn_has_code opened entry_end efn
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
  gvs[] >> strip_tac >>
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
    (package_fallback_fn tops T (K global_nonreentrant_slot)
      (SOME (mut,F,rr,"__default__",args,([] : expr list),ret,fbody))))` by
    (qspecl_then [`tops`, `T`, `K global_nonreentrant_slot`,
       `rpolicy.rpol_target`] mp_tac package_fallback_fn_shape_ok >> simp[]) >>
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
    (gvs[] >> irule external_decoder_fn_has_code >> simp[] >>
     qexists_tac `label_st` >> simp[cs_extends_refl]) >>
  `label_st.cs_blocks = [] /\ label_st.cs_current_insts = [] /\
   label_st.cs_next_var = 0 /\
   label_st.cs_current_bb = (initial_compile_state "__entry").cs_current_bb` by
    (qpat_x_assum `fresh_label _ _ = _` mp_tac >>
     simp[fresh_label_def] >> strip_tac >> gvs[] >>
     simp[initial_compile_state_def, shape_state_def]) >>
  `cs_extends label_st entry_end` by metis_tac[cs_extends_trans] >>
  drule_all cs_extends_raw_entry_label >>
  disch_then (qspec_then `"__entry"` mp_tac) >> gvs[] >> strip_tac >>
  gvs[Abbr `fbpkg`, package_fallback_fn_def, set_fallback_package_target_def] >>
  qmatch_asmsub_abbrev_tac `compile_fallback_body ce (mut = Payable) F key tr view fbody rt` >>
  `shape_state fallback_st` by metis_tac[shape_state_new_block] >>
  `cs_extends external_st fallback_st` by metis_tac[cs_extends_new_block] >>
  `cs_extends fallback_st entry_end` by
    (gvs[fallback_shape_ok_def] >>
     drule_all (SRULE [fallback_shape_ok_def] compile_fallback_body_shape) >>
     rewrite_tac[shape_step_def] >> disch_then drule >> simp[] >>
     strip_tac >> gvs[shape_extends_def]) >>
  `fn_has_code fallback_st entry_end (mk_raw_function "__entry" (all_blocks entry_end))` by
    (irule external_entry_fn_has_code >> simp[]) >>
  qexistsl_tac [`fallback_lbl`, `label_st`, `dispatch_st`, `external_st`,
    `fallback_st`, `entry_end`, `ce`, `key`, `tr`, `view`, `rt`] >>
  gvs[fallback_shape_ok_def]
QED

Theorem source_fallback_entry_check_code:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\
  FST (SND (SND (classify_functions tops))) =
    SOME (mut,F,rr,"__default__",args,[],ret,fbody) /\
  mut <> Payable /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
  fn_entry_label efn = SOME elbl ==>
  ?fb ds de opened checked.
    compile_selector_dispatch_linear
      (MAP (\(sel,lbl,z). (sel,lbl))
        (build_selectors (type_env tops) (FST (classify_functions tops))))
      fb ds = ((),de) /\
    fn_has_code ds de efn /\
    ds.cs_current_bb = elbl /\ ds.cs_current_insts = [] /\ ds.cs_next_var = 0 /\
    compile_entry_checks 0 F opened = ((),checked) /\
    fn_has_code opened checked efn /\ opened.cs_current_bb = fb /\
    opened.cs_current_insts = [] /\ ~block_is_terminated opened
Proof
  strip_tac >> drule_all classified_fallback_runtime_interval >> strip_tac >>
  Cases_on `compile_entry_checks 0 F opened` >>
  rename1 `compile_entry_checks 0 F opened = (u,checked)` >> Cases_on `u` >>
  `compile_guarded_body ce F key tr view fbody rt checked = ((),entry_end)` by
    (qpat_x_assum `compile_fallback_body _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >>
     simp[compile_fallback_body_def, compile_entry_checks_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]) >>
  `shape_state checked /\ cs_extends opened checked` by
    (qspecl_then [`0`, `F`] mp_tac compile_entry_checks_shape >>
     rewrite_tac[shape_step_def] >> disch_then drule >> simp[] >>
     strip_tac >> gvs[shape_extends_def]) >>
  `cenv_shape_ok checked ce` by metis_tac[cenv_static_ok_shape_ok] >>
  `cs_extends checked entry_end` by
    (drule compile_guarded_body_env_shape >> simp[] >>
     rewrite_tac[shape_step_def, shape_extends_def] >>
     disch_then drule >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  qexistsl_tac [`fb`, `ds`, `de`, `opened`, `checked`] >> simp[] >>
  conj_tac
  >- (irule fn_has_code_mid >> simp[] >>
      qexistsl_tac [`entry_end`, `opened`] >> simp[cs_extends_refl]) >>
  qpat_x_assum `new_block _ _ = _` mp_tac >>
  simp[new_block_def, comp_bind_def, comp_return_def] >>
  strip_tac >> gvs[block_is_terminated_def]
QED

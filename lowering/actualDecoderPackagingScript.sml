(* Ownership in the entry function, before internal-function segments. *)
Theory actualDecoderPackaging
Ancestors
  loweringShapeProps loweringShapeDefs loweringShapeRules unitShapeDefs fragExec abiDecoderCode
  vyperCompiler moduleLowering compileEnv venomInst venomExecProps
  venomPipelineDriver venomCompilerWf list rich_list

Theorem decoder_code_member_state_insts:
  abi_decoder_code_member inst st <=> MEM inst (state_insts st)
Proof
  simp[abi_decoder_code_member_def, state_insts_def, all_blocks_def,
       MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem decoder_code_member_prefix:
  cs_extends decoder_end entry_end /\ abi_decoder_code_member inst decoder_end ==>
  MEM inst (state_insts entry_end)
Proof
  strip_tac >> drule state_insts_cs_extends >>
  gvs[decoder_code_member_state_insts]
QED

Theorem external_phase_packaged_entry:
  compile_internal_fn_bodies internal_fns entry_end = (r,final) /\
  shape_state entry_end /\ EVERY internal_fn_shape_ok internal_fns /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) /\
  EVERY (\d. ~compiler_label (FST d) /\
    ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks entry_end)))
    (internal_fn_descriptors internal_fns) ==>
  ?functions. extract_context_with_internals "__entry" internal_fns final =
    SOME (mk_venom_context
      (mk_raw_function "__entry" (all_blocks entry_end) :: functions)
      (SOME "__entry"), REVERSE final.cs_data_sections)
Proof
  strip_tac >> drule_all compile_internal_fn_bodies_shape >> strip_tac >>
  drule_all package_internal_blocks_segments >> strip_tac >>
  simp[extract_context_with_internals_def, GSYM all_blocks_def] >>
  metis_tac[]
QED

Theorem external_phase_decoder_owned:
  cs_extends decoder_end entry_end /\ abi_decoder_code_member inst decoder_end ==>
  MEM inst (fn_insts (mk_raw_function "__entry" (all_blocks entry_end)))
Proof
  strip_tac >> drule_all decoder_code_member_prefix >>
  simp[fn_insts_def, mk_raw_function_def, state_insts_def,
       MEM_fn_insts_blocks_iff, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem external_phase_extracted_decoder_owned:
  compile_internal_fn_bodies internal_fns entry_end = (r,final) /\
  shape_state entry_end /\ EVERY internal_fn_shape_ok internal_fns /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) /\
  EVERY (\d. ~compiler_label (FST d) /\
    ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks entry_end)))
    (internal_fn_descriptors internal_fns) /\
  extract_context_with_internals "__entry" internal_fns final = SOME (ctx,data) /\
  cs_extends decoder_end entry_end /\ abi_decoder_code_member inst decoder_end ==>
  MEM (mk_raw_function "__entry" (all_blocks entry_end)) ctx.ctx_functions /\
  MEM inst (fn_insts (mk_raw_function "__entry" (all_blocks entry_end)))
Proof
  strip_tac >> drule_all external_phase_packaged_entry >> strip_tac >>
  gvs[mk_venom_context_def] >> irule external_phase_decoder_owned >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem run_lowering_external_decoder_owned:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info "__entry" = SOME unit /\
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    rpolicy.rpol_frontend_dispatch bucket_count fn_metadata_bytes dense_buckets
    entry_info (initial_compile_state "__entry") = ((),final) /\
  compile_internal_fn_bodies internal_fns entry_end = (r,final) /\
  shape_state entry_end /\ EVERY internal_fn_shape_ok internal_fns /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) /\
  EVERY (\d. ~compiler_label (FST d) /\
    ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks entry_end)))
    (internal_fn_descriptors internal_fns) /\
  cs_extends decoder_end entry_end /\ abi_decoder_code_member inst decoder_end ==>
  MEM (mk_raw_function "__entry" (all_blocks entry_end)) unit.cu_context.ctx_functions /\
  MEM inst (fn_insts (mk_raw_function "__entry" (all_blocks entry_end)))
Proof
  strip_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def] >>
  Cases_on `lowering_policy_ok rpolicy` >> simp[] >>
  Cases_on `extract_context_with_internals "__entry" internal_fns final` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lowering_context_ok x0` >> simp[] >> strip_tac >> gvs[] >>
  irule external_phase_extracted_decoder_owned >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem runtime_external_internal_phase_split:
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info first = ((),final) ==>
  ?fallback_lbl label_st dispatch_st external_st fallback_st entry_end r.
    fresh_label "fallback" first = (fallback_lbl,label_st) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,_). (sel,lbl)) selectors)
      fallback_lbl label_st = ((),dispatch_st) /\
    compile_external_fn_bodies external_fns dispatch_st = ((),external_st) /\
    new_block fallback_lbl external_st = (external_st.cs_current_bb,fallback_st) /\
    (case fallback_fn of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (fb_cenv,fb_pay,fb_nr,fb_key,fb_trans,fb_view,fb_body,fb_ret) =>
         compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans fb_view fb_body fb_ret)
      fallback_st = ((),entry_end) /\
    compile_internal_fn_bodies internal_fns entry_end = (r,final)
Proof
  simp[compile_generate_runtime_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >> fs[new_block_def, comp_bind_def, comp_return_def]
QED

Theorem external_runtime_phase_shape:
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn /\
  shape_state first /\
  fresh_label "fallback" first = (fallback_lbl,label_st) /\
  compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors)
    fallback_lbl label_st = ((),dispatch_st) /\
  compile_external_fn_bodies external_fns dispatch_st = ((),external_st) /\
  new_block fallback_lbl external_st = (old_lbl,fallback_st) /\
  (case fallback_fn of
     NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
   | SOME (fb_cenv,fb_pay,fb_nr,fb_key,fb_trans,fb_view,fb_body,fb_ty) =>
       compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans fb_view fb_body fb_ty)
    fallback_st = ((),entry_end) ==>
  shape_state entry_end /\ cs_extends first entry_end /\
  shape_extends F jump_label_ok first entry_end
Proof
  strip_tac >> drule_all runtime_entry_prefix_shape >>
  qmatch_goalsub_abbrev_tac `shape_step F jump_label_ok _ prefix _` >>
  `prefix first = ((),entry_end)` by
    simp[Abbr `prefix`, comp_bind_def, comp_ignore_bind_def] >>
  simp[shape_step_def] >> disch_then drule >>
  simp[] >> simp[shape_extends_def]
QED

Theorem runtime_external_boundary:
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info first = ((),final) /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn /\
  shape_state first ==>
  ?fallback_lbl label_st dispatch_st external_st fallback_st entry_end r.
    fresh_label "fallback" first = (fallback_lbl,label_st) /\
    compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) selectors)
      fallback_lbl label_st = ((),dispatch_st) /\
    compile_external_fn_bodies external_fns dispatch_st = ((),external_st) /\
    new_block fallback_lbl external_st = (external_st.cs_current_bb,fallback_st) /\
    (case fallback_fn of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (fb_cenv,fb_pay,fb_nr,fb_key,fb_trans,fb_view,fb_body,fb_ty) =>
         compile_fallback_body fb_cenv fb_pay fb_nr fb_key fb_trans fb_view fb_body fb_ty)
      fallback_st = ((),entry_end) /\
    compile_internal_fn_bodies internal_fns entry_end = (r,final) /\
    shape_state entry_end /\ cs_extends first entry_end /\
  shape_extends F jump_label_ok first entry_end
Proof
  strip_tac >> drule runtime_external_internal_phase_split >> strip_tac >>
  drule_all external_runtime_phase_shape >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

Theorem runtime_packaged_external_boundary:
  compile_generate_runtime selectors external_fns internal_fns fallback_fn
    Linear bucket_count fn_metadata_bytes dense_buckets entry_info
    (initial_compile_state "__entry") = ((),final) /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) selectors /\
  EVERY external_fn_shape_ok external_fns /\ fallback_shape_ok fallback_fn /\
  EVERY internal_fn_shape_ok internal_fns /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) ==>
  ?entry_end r functions.
    compile_internal_fn_bodies internal_fns entry_end = (r,final) /\
    shape_state entry_end /\
    shape_extends F jump_label_ok (initial_compile_state "__entry") entry_end /\
    extract_context_with_internals "__entry" internal_fns final =
      SOME (mk_venom_context
        (mk_raw_function "__entry" (all_blocks entry_end) :: functions)
        (SOME "__entry"), REVERSE final.cs_data_sections)
Proof
  strip_tac >>
  `shape_state (initial_compile_state "__entry")` by
    MATCH_ACCEPT_TAC shape_state_initial_compile_state >>
  drule_all runtime_external_boundary >> strip_tac >>
  drule runtime_entry_blocks_shape >> strip_tac >>
  `EVERY (\d. ~compiler_label (FST d) /\
    ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks entry_end)))
      (internal_fn_descriptors internal_fns)` by
    (rewrite_tac[EVERY_MEM] >> rpt strip_tac >> BETA_TAC >>
     irule internal_name_not_entry_label >> simp[] >>
     fs[EVERY_MEM]) >>
  drule_all external_phase_packaged_entry >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem external_entry_fn_has_code:
  cs_extends first last /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks last)) ==>
  fn_has_code first last (mk_raw_function "__entry" (all_blocks last))
Proof
  strip_tac >> simp[fn_has_code_def, mk_raw_function_def] >> conj_tac
  >- (rpt strip_tac >> irule MEM_lookup_block >> simp[] >>
      fs[emitted_blocks_def, all_blocks_def] >>
      metis_tac[MEM_TAKE, MEM_REVERSE]) >>
  qexists_tac `<|bb_label := last.cs_current_bb; bb_instructions := last.cs_current_insts|>` >>
  simp[] >> irule MEM_lookup_block >> simp[all_blocks_def]
QED

Theorem external_decoder_fn_has_code:
  cs_extends first decoder_start /\ cs_extends decoder_start decoder_end /\
  cs_extends decoder_end entry_end /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks entry_end)) ==>
  fn_has_code decoder_start decoder_end (mk_raw_function "__entry" (all_blocks entry_end))
Proof
  strip_tac >> irule fn_has_code_mid >> simp[] >>
  qexistsl_tac [`entry_end`, `first`] >> simp[] >>
  irule external_entry_fn_has_code >> simp[] >>
  metis_tac[cs_extends_trans]
QED

Theorem checked_pipeline_input_wf:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out ==>
  unit_wf unit
Proof
  Cases_on `unit_wf unit` >> simp[run_venom_pipeline_def]
QED

Theorem distinct_flat_member[local]:
  !xss xs. ALL_DISTINCT (FLAT xss) /\ MEM xs xss ==> ALL_DISTINCT xs
Proof
  Induct >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem checked_pipeline_entry_labels:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out /\
  MEM (mk_raw_function "__entry" (all_blocks entry_end)) unit.cu_context.ctx_functions ==>
  ALL_DISTINCT (MAP (\bb. bb.bb_label) (all_blocks entry_end))
Proof
  strip_tac >> drule checked_pipeline_input_wf >>
  simp[unit_wf_def, unit_labels_wf_def, unit_label_namespace_def] >> strip_tac >>
  drule distinct_flat_member >>
  disch_then (qspec_then `fn_labels (mk_raw_function "__entry" (all_blocks entry_end))` mp_tac) >>
  impl_tac >- (simp[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[fn_labels_def, mk_raw_function_def]
QED

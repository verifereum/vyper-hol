(* Packaging preserves the compiler prefix as code in the entry function. *)
Theory entryCodeContainment
Ancestors
  fragExec loweringShapeDefs loweringShapeProps vyperCompiler
  venomExecProofs compileEnv list venomInst

Theorem all_blocks_fn_has_code:
  fn.fn_blocks = all_blocks st /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) ==>
  fn_has_code (initial_compile_state "__entry") st fn
Proof
  strip_tac >> rewrite_tac[fn_has_code_def] >> conj_tac
  >- (simp[emitted_blocks_def, initial_compile_state_def] >>
      rpt strip_tac >> irule MEM_lookup_block >>
      gvs[all_blocks_def]) >>
  qexists `<| bb_label := st.cs_current_bb;
              bb_instructions := st.cs_current_insts |>` >>
  simp[] >> irule MEM_lookup_block >> gvs[all_blocks_def]
QED

Theorem extracted_entry_prefix_blocks:
  all_blocks st_final = all_blocks entry_st ++ FLAT segs /\
  LIST_REL internal_segment_ok (internal_fn_descriptors internal_fns) segs /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) /\
  EVERY (\d. ~compiler_label (FST d) /\
             ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks entry_st)))
        (internal_fn_descriptors internal_fns) /\
  extract_context_with_internals "__entry" internal_fns st_final =
    SOME (ctx, data) /\
  lookup_function "__entry" ctx.ctx_functions = SOME efn ==>
  efn.fn_blocks = all_blocks entry_st
Proof
  strip_tac >> drule_all package_internal_blocks_segments >> strip_tac >>
  qpat_x_assum `extract_context_with_internals _ _ _ = _` mp_tac >>
  simp_tac bool_ss [extract_context_with_internals_def, LET_THM] >>
  rewrite_tac[GSYM all_blocks_def] >> asm_rewrite_tac[] >>
  simp[mk_venom_context_def, lookup_function_def, FIND_thm,
       mk_raw_function_def] >> strip_tac >>
  gvs[lookup_function_def, FIND_thm, mk_raw_function_def]
QED

Theorem extracted_entry_body_has_code:
  all_blocks st_final = all_blocks entry_st ++ FLAT segs /\
  LIST_REL internal_segment_ok (internal_fn_descriptors internal_fns) segs /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors internal_fns)) /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors internal_fns) /\
  all_blocks entry_st <> [] /\
  (HD (all_blocks entry_st)).bb_label = "__entry" /\
  EVERY jump_label_ok (TL (MAP (\bb. bb.bb_label) (all_blocks entry_st))) /\
  extract_context_with_internals "__entry" internal_fns st_final =
    SOME (ctx, data) /\
  lookup_function "__entry" ctx.ctx_functions = SOME efn /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) efn.fn_blocks) /\
  cs_extends (initial_compile_state "__entry") sa /\
  cs_extends sa se /\ cs_extends se entry_st ==>
  fn_has_code sa se efn
Proof
  strip_tac >>
  `EVERY (\d. ~compiler_label (FST d) /\
       ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks entry_st)))
      (internal_fn_descriptors internal_fns)` by
    (rewrite_tac[EVERY_MEM] >> rpt strip_tac >>
     BETA_TAC >> irule internal_name_not_entry_label >> gvs[EVERY_MEM]) >>
  drule_all extracted_entry_prefix_blocks >> strip_tac >>
  `fn_has_code (initial_compile_state "__entry") entry_st efn` by
    (irule all_blocks_fn_has_code >> simp[]) >>
  irule fn_has_code_mid >> simp[] >>
  qexistsl [`entry_st`, `initial_compile_state "__entry"`] >> simp[]
QED

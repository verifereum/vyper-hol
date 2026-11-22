(* Transfer runtime label checks from the generators to extracted code. *)
Theory runtimeLabelRunners
Ancestors
  runtimeLabelInvariant runtimeLabelGenerators entryExtractionCodePredicate
  entryCodePredicate loweringShapeDefs compileVyper vyperCompiler venomInst list

Theorem rb_state_entry_code_for[local]:
  (rb_state_ok_for source_checks) st <=> entry_code_pred (source_inst_ok source_checks) st
Proof
  simp[rb_state_ok_for_def, state_insts_def, all_blocks_def,
       entry_code_pred_def, EVERY_FLAT, EVERY_MAP] >> metis_tac[]
QED

Theorem rb_extract_context_for[local]:
  (rb_state_ok_for source_checks) st /\
  extract_context_with_internals entry internals st = SOME (ctx,data) /\
  MEM fn ctx.ctx_functions ==>
  EVERY (source_inst_ok source_checks) (fn_insts fn)
Proof
  simp[rb_state_entry_code_for] >> strip_tac >>
  drule_all entry_code_extracted_context >> simp[]
QED

Theorem rb_run_lowering_for:
  (rb_step_for source_checks) (K T) (compile_generate_runtime sels exts ints fb
    rp.rpol_frontend_dispatch bc width buckets info) /\
  run_lowering sels exts ints fb rp bc width buckets info entry = SOME unit /\
  MEM fn unit.cu_context.ctx_functions ==>
  EVERY (source_inst_ok source_checks) (fn_insts fn)
Proof
  simp[run_lowering_def] >> strip_tac >> pairarg_tac >>
  gvs[AllCaseEqs()] >>
  `(rb_state_ok_for source_checks) st1` by
    (qpat_x_assum `(rb_step_for source_checks) _ _` mp_tac >>
     simp[rb_step_for_def] >> disch_then (qspec_then `initial_compile_state entry` mp_tac) >>
     simp[rb_state_ok_for_def, state_insts_def, all_blocks_def, initial_compile_state_def]) >>
  drule_at (Pos (el 2)) rb_extract_context_for >> disch_then drule_all >> simp[]
QED

Theorem rb_run_grouped_lowering_for:
  (rb_step_for source_checks) (K T) (compile_generate_grouped_runtime groups ints fb) /\
  run_grouped_lowering groups ints fb rp entry = SOME unit /\
  MEM fn unit.cu_context.ctx_functions ==>
  EVERY (source_inst_ok source_checks) (fn_insts fn)
Proof
  simp[run_grouped_lowering_def] >> strip_tac >> pairarg_tac >>
  gvs[AllCaseEqs()] >>
  `(rb_state_ok_for source_checks) st1` by
    (qpat_x_assum `(rb_step_for source_checks) _ _` mp_tac >>
     simp[rb_step_for_def] >> disch_then (qspec_then `initial_compile_state entry` mp_tac) >>
     simp[rb_state_ok_for_def, state_insts_def, all_blocks_def, initial_compile_state_def]) >>
  drule_at (Pos (el 2)) rb_extract_context_for >> disch_then drule_all >> simp[]
QED

Theorem rb_build_selectors_for:
  !fs. EVERY (\(sel,lbl,tz). (rb_operand_ok_for source_checks) (Label lbl)) (build_selectors tenv fs)
Proof
  Induct >> simp[build_selectors_def] >> gen_tac >> PairCases_on `h` >>
  gvs[build_selectors_def, compute_selector_def, rb_operand_ok_for_def]
QED

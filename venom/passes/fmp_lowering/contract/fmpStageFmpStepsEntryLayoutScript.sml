Theory fmpStageFmpStepsEntryLayout
Ancestors
  fmpStageRel venomExecSemantics irSupply venomFnScheduleRunner
  venomFnScheduleRunnerProps contextCodegenRel
  fmpStageOpBase fmpStageOpBaseActual fmpStepBridge concretizeStageLookup
  fmpStepLayout fmpStepRestrictionClosure fmpAnalysisProps
  fmpLowerDefs o1PassContract venomExecProofs
  venomInst list finite_map

Theorem fmp_entry_source_shape:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  C.ctx_entry = SOME name /\
  lookup_function name C.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\
  enters_block fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s1 ==>
  fn.fn_name = name /\ entry_fn_no_params fn /\
  s1 = vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>
Proof
  strip_tac >>
  `fn.fn_name = name` by metis_tac[lookup_function_name] >>
  `o1_fn_shape C fn` by
    (gvs[fmp_stage_ctx_def, o1_ctx_shape_def, EVERY_MEM] >>
     metis_tac[lookup_function_MEM]) >>
  gvs[o1_fn_shape_def] >>
  Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
  `phi_prefix_length h.bb_instructions = 0 /\
   (!s. eval_phis s h.bb_instructions = OK s)` by
    (qpat_x_assum `first_block_no_phi fn` mp_tac >>
     simp[first_block_no_phi_def] >> Cases_on `h.bb_instructions` >>
     simp[phi_prefix_length_def, eval_phis_def]) >>
  gvs[enters_block_def, lookup_block_def, FIND_thm]
QED

Theorem fmp_entry_split_empty[local]:
  entry_fn_no_params fn /\
  split_fmp_entry fn = SOME (FmpEntryLayout users pc tail) ==>
  users = [] /\ pc = NONE
Proof
  strip_tac >>
  `pc = NONE` by metis_tac[split_fmp_entry_no_params_retpc] >> simp[] >>
  drule split_fmp_entry_users >> strip_tac >>
  drule split_fmp_entry_reconstruct >> strip_tac >>
  gvs[entry_fn_no_params_def, fn_insts_def, fn_insts_blocks_def,
      EVERY_APPEND] >>
  Cases_on `users` >> gvs[is_param_opcode_def]
QED

Theorem fmp_entry_root_position:
  fn_is_context_entry ctx fn /\ entry_fn_no_params fn /\
  fn_entry_label fn = SOME lbl ==>
  fmp_stage_root infos ctx fn = NONE \/
  fmp_stage_root infos ctx fn = SOME (lbl,0)
Proof
  simp[fmp_stage_root_def] >> rpt strip_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
  Cases_on `split_fmp_entry fn` >> simp[] >>
  Cases_on `x` >> simp[] >>
  drule_all fmp_entry_split_empty >> strip_tac >> gvs[] >>
  simp[callLayoutDefsTheory.OPTION_TO_LIST_def]
QED

Theorem fmp_entry_target_block:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn_entry_label fn = SOME lbl ==>
  ?bb. lookup_block lbl fn'.fn_blocks = SOME bb
Proof
  strip_tac >>
  `fn_entry_label fn' = SOME lbl` by
    (gvs[fmp_stage_lowered_def] >>
     `fmp_lower_function ctx sp fn = SOME (fn',sp')` by
       simp[fmp_lower_function_def] >>
     drule fmp_lower_function_preserves_entry_label >> simp[]) >>
  Cases_on `fn'.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]
QED

Theorem fmp_entry_initial_prefix:
  fmp_stage_lowered infos ctx runner fn fn' /\
  fn.fn_fmp_signature = NONE /\ fn_is_context_entry ctx fn /\
  entry_fn_no_params fn /\ fn_entry_label fn = SOME lbl /\
  fmp_stage_root infos ctx fn = SOME (lbl,0) ==>
  ?bb id tail.
    lookup_block lbl fn'.fn_blocks = SOME bb /\
    bb.bb_instructions = mk_inst id INITIAL_FMP [] [runner] :: tail
Proof
  strip_tac >>
  gvs[fmp_stage_lowered_def, fmp_stage_root_def, AllCaseEqs()] >>
  drule_all fmp_entry_split_empty >> strip_tac >> gvs[] >>
  gvs[fmp_lower_function_with_info_def, AllCaseEqs(),
      fmp_make_root_layout_def, fmp_install_root_def,
      fmp_checked_seal_def, fmp_seal_def,
      callLayoutDefsTheory.OPTION_TO_LIST_def] >>
  drule fmp_lower_blocks_preserves_labels >> simp[] >> strip_tac >>
  simp[lookup_block_def, FIND_thm] >> metis_tac[]
QED

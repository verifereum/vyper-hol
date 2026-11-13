Theory fmpStageFmpStepsEntryInitialization
Ancestors
  fmpStageFmpStepsEntryAnalysis fmpStageFmpStepsEntryState
  fmpStageFmpStepsRestoreControl
  fmpStageRel fmpLedgerProps venomState finite_map words list

Theorem fmp_entry_frame[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  wf_function fn /\ fn_entry_label fn = SOME lbl /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  (fmp_stage_root infos ctx fn = NONE \/
   fmp_stage_root infos ctx fn = SOME (lbl,0)) /\
  idx = (if fmp_stage_root infos ctx fn = NONE then 0 else 1) /\
  (fmp_stage_root infos ctx fn = SOME (lbl,0) ==>
   FLOOKUP vars runner = SOME vs'.vs_initial_fmp) ==>
  fmp_frame_rel FEMPTY (w2n vs'.vs_initial_fmp) (w2n fmp)
    (w2n fmp) (w2n vs'.vs_initial_fmp) (w2n vs'.vs_initial_fmp) F
    fn fn' [] FEMPTY entry_taint.t_var
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    (vs' with <|vs_vars := vars; vs_prev_bb := NONE;
                vs_current_bb := lbl; vs_inst_idx := idx|>)
Proof
  strip_tac >>
  drule fmp_entry_state_fields >> strip_tac >>
  simp[fmp_frame_rel_def] >>
  qexistsl_tac [`infos`, `ctx`, `runner`] >>
  simp[fmp_stage_tidx_def, fmp_frame_covers_def, fmp_ledger_link_def] >>
  gvs[fmp_stage_ctx_def] >>
  drule_all fmp_stage_entry_analysis >> strip_tac >>
  qexistsl_tac [`env`, `states`, `st`] >>
  simp[lookup_var_def] >>
  qexists_tac `[]` >> simp[fmp_ledger_ok_def]
QED

Theorem fmp_entry_relation[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  wf_function fn /\ fn_entry_label fn = SOME lbl /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  (fmp_stage_root infos ctx fn = NONE \/
   fmp_stage_root infos ctx fn = SOME (lbl,0)) /\
  idx = (if fmp_stage_root infos ctx fn = NONE then 0 else 1) /\
  (fmp_stage_root infos ctx fn = SOME (lbl,0) ==>
   FLOOKUP vars runner = SOME vs'.vs_initial_fmp) ==>
  fmp_stage_rel D C' FEMPTY (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
    [] [] FEMPTY entry_taint fn
    (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    (w2n vs'.vs_initial_fmp)
    (vs' with <|vs_vars := vars; vs_prev_bb := NONE;
                vs_current_bb := lbl; vs_inst_idx := idx|>) []
Proof
  strip_tac >>
  drule fmp_entry_shared_fields >> simp[] >> strip_tac >>
  simp[fmp_stage_rel_def, fmp_sites_ok_def, fmp_saved_rel_def,
       fmp_frame_base_def, fmp_frame_lo_def] >>
  (reverse conj_tac >- metis_tac[]) >>
  mp_tac fmp_entry_frame >> simp[]
QED

Theorem fmp_stage_entry_from_layout:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fn.fn_name = name /\ wf_function fn /\
  fn_entry_label fn = SOME lbl /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_function name C'.ctx_functions = SOME fn' /\
  lookup_block lbl fn'.fn_blocks = SOME bb' /\
  (fmp_stage_root infos ctx fn = NONE \/
   fmp_stage_root infos ctx fn = SOME (lbl,0)) /\
  (fmp_stage_root infos ctx fn = SOME (lbl,0) ==>
   ?id rest. bb'.bb_instructions = mk_inst id INITIAL_FMP [] [runner]::rest) ==>
  ?n t1.
    (!k. fmp_target_run k C' name
      (vs' with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) n t1) /\
    fmp_stage_rel D C' FEMPTY (w2n vs'.vs_initial_fmp) (w2n fmp) eom F
      [] [] FEMPTY entry_taint fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
      (w2n vs'.vs_initial_fmp) t1 []
Proof
  `vs' with <|vs_vars := vs'.vs_vars; vs_prev_bb := NONE;
      vs_current_bb := lbl; vs_inst_idx := 0|> =
   vs' with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    simp[venom_state_component_equality] >>
  strip_tac
  >- (qexistsl_tac [`0`,
        `vs' with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`] >>
      conj_tac
      >- (irule fmp_restore_target_run_zero >> simp[] >> metis_tac[]) >>
      mp_tac (Q.INST [`idx` |-> `0`, `vars` |-> `vs'.vs_vars`]
        fmp_entry_relation) >> simp[]) >>
  qexistsl_tac [`1`, `(update_var runner vs'.vs_initial_fmp vs') with
    <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 1|>`] >>
  conj_tac >- metis_tac[fmp_entry_run_root] >>
  simp[update_var_def] >>
  mp_tac (Q.INST [`idx` |-> `1`,
    `vars` |-> `vs'.vs_vars |+ (runner,vs'.vs_initial_fmp)`]
    fmp_entry_relation) >> simp[FLOOKUP_UPDATE]
QED

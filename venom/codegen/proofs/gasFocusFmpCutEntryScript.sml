(* Initialize the selected FMP frame at the fixed filling, before any
   source instruction (and just after the target root, when present). *)
Theory gasFocusFmpCutEntry
Ancestors
  gasFocusFmpStagePin fmpStageFmpStepsEntryLayout
  fmpStageFmpStepsEntryAnalysis fmpStageFmpStepsEntryState
  fmpStageFmpStepsRestoreControl o1LowerDloadSourceEntry
  fmpStageRel fmpLedgerProps fmpLowerSequenceExec o1PassContract
  o1LowerDloadShared o1LowerDloadRelocationKernel venomState
  unitTransformDefs ptrDiscipline finite_map words list

Theorem cut_entry_frame[local]:
  o1_run_state_ok v /\ w2n v.vs_initial_fmp <= w2n fmp /\
  wf_function fn /\ fn_entry_label fn = SOME lbl /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  (fmp_stage_root infos ctx fn = NONE \/
   fmp_stage_root infos ctx fn = SOME (lbl,0)) /\
  idx = (if fmp_stage_root infos ctx fn = NONE then 0 else 1) /\
  (fmp_stage_root infos ctx fn = SOME (lbl,0) ==>
     FLOOKUP vars runner = SOME v.vs_initial_fmp) ==>
  fmp_frame_rel FEMPTY (w2n v.vs_initial_fmp) (w2n fmp)
    (w2n fmp) (w2n v.vs_initial_fmp) (w2n v.vs_initial_fmp) F
    fn fn' [] FEMPTY entry_taint.t_var
    (v with <|vs_fmp := fmp; vs_initial_fmp := fmp;
              vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    (v with <|vs_vars := vars; vs_prev_bb := NONE;
              vs_current_bb := lbl; vs_inst_idx := idx|>)
Proof
  strip_tac >> simp[fmp_frame_rel_def] >>
  qexistsl [`infos`, `ctx`, `runner`] >>
  gvs[o1_run_state_ok_def, o1_initial_state_ok_def,
      fmp_stage_tidx_def, fmp_env_rel_def, fmp_params_rel_def,
      fmp_value_rel_def, ld_value_agree_def, word_agree_except_def,
      fmp_frontier_rel_def, fmp_frame_covers_def, fmp_ledger_link_def] >>
  drule_all fmp_stage_entry_analysis >> strip_tac >>
  qexistsl [`env`, `states`, `st`] >> simp[lookup_var_def] >>
  qexists `[]` >> simp[fmp_ledger_ok_def, fmp_ledger_link_def]
QED

Theorem cut_entry_stage[local]:
  o1_run_state_ok v /\ w2n v.vs_initial_fmp <= w2n fmp /\
  wf_function fn /\ fn_entry_label fn = SOME lbl /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  lookup_function fn.fn_name C4.ctx_functions = SOME fn' /\
  (fmp_stage_root infos ctx fn = NONE \/
   fmp_stage_root infos ctx fn = SOME (lbl,0)) /\
  idx = (if fmp_stage_root infos ctx fn = NONE then 0 else 1) /\
  (fmp_stage_root infos ctx fn = SOME (lbl,0) ==>
     FLOOKUP vars runner = SOME v.vs_initial_fmp) ==>
  fmp_stage_rel D C4 FEMPTY (w2n v.vs_initial_fmp) (w2n fmp) eom F
    [] [] FEMPTY entry_taint fn
    (v with <|vs_fmp := fmp; vs_initial_fmp := fmp;
              vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
    (w2n v.vs_initial_fmp)
    (v with <|vs_vars := vars; vs_prev_bb := NONE;
              vs_current_bb := lbl; vs_inst_idx := idx|>) []
Proof
  strip_tac >>
  simp[fmp_stage_rel_def, fmp_sites_ok_def, fmp_saved_rel_def,
       fmp_frame_base_def, fmp_frame_lo_def, fmp_ld_sites_def,
       FMAP_MAP2_FEMPTY, ld_memory_agree_empty] >>
  (conj_tac >- (mp_tac cut_entry_frame >> simp[])) >>
  mp_tac (Q.INST [`s` |-> `v`, `A` |-> `v.vs_call_ctx.cc_address`,
                   `tn` |-> `entry_taint`] ld_shared_agree_refl) >>
  simp[ld_shared_agree_def]
QED

Theorem focus_fmp_cut_entry:
  ctx_pass_stage rpolicy (CFP_Simple VP_FmpLowering)
    (o1_walk_view rpolicy 3) C3 C4 /\
  C3.ctx_entry = SOME name /\ lookup_function name C3.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl /\ wf_function fn /\ entry_fn_no_params fn /\
  first_block_no_phi fn /\ fn.fn_fmp_signature = NONE /\ pre_fmp_ops fn /\
  o1_run_state_ok v /\ w2n v.vs_initial_fmp <= w2n fmp /\
  u = v with <|vs_fmp := fmp; vs_initial_fmp := fmp|> /\
  enters_block fn
    (u with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) s ==>
  ?fn' p t.
    lookup_function name C4.ctx_functions = SOME fn' /\
    fn_entry_label fn' = SOME lbl /\
    (!k. fmp_target_run k C4 name
      (v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) p t) /\
    fmp_stage_rel D C4 FEMPTY (w2n v.vs_initial_fmp) (w2n fmp) eom F
      [] [] FEMPTY entry_taint fn s (w2n v.vs_initial_fmp) t [] /\
    ((p = 0 /\
      t = v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>) \/
     (p = 1 /\ ?bb id runner tail.
       lookup_block lbl fn'.fn_blocks = SOME bb /\
       bb.bb_instructions = mk_inst id INITIAL_FMP [] [runner]::tail /\
       t = (update_var runner v.vs_initial_fmp v) with
         <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 1|>))
Proof
  strip_tac >> drule_all focus_fmp_selected_root_pin >>
  disch_then (qx_choose_then `fn'` (qx_choose_then `infos` (
    qx_choose_then `ctx` (qx_choose_then `runner` strip_assume_tac)))) >>
  `fn.fn_name = name` by metis_tac[fmpAnalysisPropsTheory.lookup_function_name] >>
  `s = u with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
    (mp_tac (Q.INST [`f` |-> `fn`, `vs` |-> `u`, `t` |-> `s`]
               dload_no_phi_entry) >> simp[]) >>
  `fn_is_context_entry ctx fn` by simp[] >>
  mp_tac (Q.INST [`infos` |-> `infos`] fmp_entry_root_position) >>
  (impl_tac >- simp[]) >> strip_tac
  >- (drule_all fmp_entry_target_block >> strip_tac >>
      qexistsl [`fn'`, `0`,
        `v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>`] >>
      simp[] >> conj_tac
      >- (irule fmp_restore_target_run_zero >> simp[] >> metis_tac[]) >>
      `v with <|vs_vars := v.vs_vars; vs_prev_bb := NONE;
                vs_current_bb := lbl; vs_inst_idx := 0|> =
       v with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` by
        simp[venom_state_component_equality] >>
      mp_tac (Q.INST [`idx` |-> `0`, `vars` |-> `v.vs_vars`]
                cut_entry_stage) >> simp[]) >>
  drule_all fmp_entry_initial_prefix >>
  disch_then (qx_choose_then `bb` (qx_choose_then `id` (
    qx_choose_then `tail` strip_assume_tac))) >>
  qexistsl [`fn'`, `1`, `(update_var runner v.vs_initial_fmp v) with
    <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 1|>`] >>
  simp[] >> conj_tac
  >- metis_tac[fmp_entry_run_root] >>
  reverse conj_tac >- metis_tac[] >>
  simp[update_var_def] >>
  mp_tac (Q.INST [`idx` |-> `1`,
    `vars` |-> `v.vs_vars |+ (runner,v.vs_initial_fmp)`] cut_entry_stage) >>
  simp[FLOOKUP_UPDATE] >> metis_tac[]
QED

Theory fmpStageFmpStepsRestoreFrame
Ancestors
  fmpStageRel fmpLowerSequenceExec venomState finite_map list

(* Reconstruct the same lowering witness after its point's restore.  The
   cut and freshness boundaries supply only the fields that change. *)
Theorem fmp_restore_postroot_frame:
  fmp_stage_lowered infos ctx runner fn fn' /\
  plan = fmp_stage_plan infos ctx fn /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  insts = (case lookup_block s.vs_current_bb fn.fn_blocks of
             SOME bb => bb.bb_instructions | NONE => []) /\
  (s.vs_current_bb,s.vs_inst_idx) IN FDOM plan /\
  ~(s.vs_current_bb = rl /\ s.vs_inst_idx < rp) /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  t.vs_inst_idx = fmp_stage_tidx plan (SOME (rl,rp))
    s.vs_current_bb insts s.vs_inst_idx /\
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
  s.vs_block_ctx = t.vs_block_ctx /\
  s.vs_data_section = t.vs_data_section /\ s.vs_labels = t.vs_labels /\
  s.vs_code = t.vs_code /\ s.vs_prev_hashes = t.vs_prev_hashes /\
  w2n s.vs_initial_fmp = raw0 /\ w2n t.vs_initial_fmp = fmp0 /\
  fmp_frontier_rel fmp0 raw0 lo s.vs_fmp /\
  cut <= lo /\ elo <= cut /\ fmp0 <= cut /\ eb <= w2n s.vs_fmp /\
  t1 = ((update_var runner (n2w cut) t) with
          vs_inst_idx := SUC t.vs_inst_idx) /\
  fmp_env_rel sm' fn
    (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
    G tv s t1 /\ fmp_params_rel sm' PG s t1 /\
  (!b z c id. FLOOKUP sm' (b,z) = SOME (c,id) ==>
    (eb <= b <=> elo <= c) /\ (b < eb ==> c + z <= elo /\ b + z <= eb)) /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  fmp_reclaim_states infos fn = SOME states /\
  df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st /\
  fmp_frame_covers sm' env eb cut G /\
  fmp_ledger_ok (fn_insts fn) env t1 cut ks /\
  MAP (\r. r.fr_mark) ks =
    SND (fmp_pop_at infos fn (liveness_analyze fn) env
      (s.vs_current_bb,s.vs_inst_idx) (EL s.vs_inst_idx insts) st) /\
  EVERY (\r. elo <= r.fr_lo) ks /\ fmp_ledger_link sm' eb cut ks ==>
  fmp_frame_rel sm' fmp0 raw0 eb elo cut T fn fn' PG G tv s t1
Proof
  rpt strip_tac >>
  `fmp_frontier_rel fmp0 raw0 cut s.vs_fmp` by
    metis_tac[fmp_restore_frontier] >>
  gvs[] >>
  simp[fmp_frame_rel_def] >>
  qexistsl [`infos`, `ctx`, `runner`] >>
  simp[venomStateTheory.update_var_def] >>
  conj_tac >- metis_tac[] >>
  IF_CASES_TAC >- gvs[] >>
  simp[venomStateTheory.lookup_var_def, FLOOKUP_UPDATE] >>
  qexists `ks` >> gvs[venomStateTheory.update_var_def]
QED

Theory fmpStageFmpStepsRetpcFrameCore
Ancestors
  fmpStageRel venomState finite_map list

Theorem fmp_retpc_frame_reconstruct:
  plan = fmp_stage_plan infos ctx fn /\
  root = fmp_stage_root infos ctx fn /\
  insts = (case lookup_block s.vs_current_bb fn.fn_blocks of
             SOME bb => bb.bb_instructions | NONE => []) /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  t.vs_inst_idx = fmp_stage_tidx plan root s.vs_current_bb insts s.vs_inst_idx /\
  fmp_env_rel sm fn (live_vars_at (liveness_analyze fn)
    s.vs_current_bb s.vs_inst_idx) G tv s t /\
  fmp_params_rel sm PG s t /\
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
  s.vs_block_ctx = t.vs_block_ctx /\
  s.vs_data_section = t.vs_data_section /\ s.vs_labels = t.vs_labels /\
  s.vs_code = t.vs_code /\ s.vs_prev_hashes = t.vs_prev_hashes /\
  w2n s.vs_initial_fmp = raw0 /\ w2n t.vs_initial_fmp = fmp0 /\
  fmp_frontier_rel fmp0 raw0 lo s.vs_fmp /\ elo <= lo /\
  eb <= w2n s.vs_fmp /\
  (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==>
    (eb <= b <=> elo <= c) /\ (b < eb ==> c + z <= elo /\ b + z <= eb)) /\
  (case root of NONE => lo = elo | SOME (rl,rp) =>
    ?env states st stack.
      fmp_base_analyze (fn_insts fn) = SOME env /\
      fmp_reclaim_states infos fn = SOME states /\
      df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st /\
      stack = st.frs_stack /\ fmp_frame_covers sm env eb lo G /\
      (if s.vs_current_bb = rl /\ s.vs_inst_idx < rp then
         lo = elo /\ stack = [] /\
         (fn_is_context_entry ctx fn ==> fmp0 = elo) /\
         (~fn_is_context_entry ctx fn ==>
           LENGTH s.vs_params = LENGTH (fn_user_param_insts fn) /\
           LENGTH s.vs_params < LENGTH t.vs_params /\
           EL (LENGTH s.vs_params) t.vs_params = n2w elo)
       else lookup_var runner t = SOME (n2w lo) /\
         ?regions. fmp_ledger_ok (fn_insts fn) env t lo regions /\
           MAP (\r. r.fr_mark) regions = stack /\
           EVERY (\r. elo <= r.fr_lo) regions /\
           fmp_ledger_link sm eb lo regions)) /\
  s1 = update_var pc s.vs_return_pc_token s /\
  s2 = s1 with vs_inst_idx := SUC s.vs_inst_idx /\
  ((root = NONE /\
     t1 = update_var pc t.vs_return_pc_token t with vs_inst_idx := ti) \/
   (root = SOME (s.vs_current_bb,SUC s.vs_inst_idx) /\ pc <> runner /\
     t1 = update_var pc t.vs_return_pc_token
       (update_var runner (n2w lo) t) with vs_inst_idx := ti)) /\
  ti = fmp_stage_tidx plan root s.vs_current_bb insts (SUC s.vs_inst_idx) /\
  fmp_env_rel sm fn (live_vars_at (liveness_analyze fn)
    s.vs_current_bb (SUC s.vs_inst_idx)) G1 tv1 s2 t1 /\
  fmp_params_rel sm PG s2 t1 /\
  (!rl rp env states st.
    root = SOME (rl,rp) /\
    fmp_base_analyze (fn_insts fn) = SOME env /\
    fmp_reclaim_states infos fn = SOME states /\
    df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st ==>
    (?st1. df_at NONE states s.vs_current_bb (SUC s.vs_inst_idx) = SOME st1 /\
           st1.frs_stack = []) /\
    fmp_frame_covers sm env eb lo G1 /\
    fmp_ledger_ok (fn_insts fn) env t1 lo [] /\
    fmp_ledger_link sm eb lo []) ==>
  fmp_frame_rel sm fmp0 raw0 eb elo lo F fn fn' PG G1 tv1 s2 t1
Proof
  rpt strip_tac >>
  simp[fmp_frame_rel_def] >>
  qexistsl_tac [`infos`, `ctx`, `runner`] >>
  gvs[update_var_def] >- metis_tac[] >>
  qpat_x_assum `SOME _ = fmp_stage_root _ _ _`
    (fn th => fs[GSYM th]) >>
  conj_tac >- metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `st1` >>
  gvs[lookup_var_def, FLOOKUP_UPDATE] >>
  qexists_tac `[]` >> simp[]
QED

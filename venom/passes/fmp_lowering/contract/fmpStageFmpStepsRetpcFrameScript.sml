Theory fmpStageFmpStepsRetpcFrame
Ancestors
  fmpStageFmpStepsRetpcFrameCore fmpStageFmpStepsRetpcAnalysis
  fmpStageFmpStepsRetpcState fmpStageReclaimSound
  fnBlockPlanStaticOffsetLive cfgWf venomWfProps venomExecProofs
  fmpLedgerProps contextCodegenRel venomWf o1PassContract
  cfgDefs venomInst fmpStageRel venomState ptrDiscipline
  fmpStageFmpStepsRetpcPreservation finite_map list pred_set

Theorem fmp_retpc_runner_dead[local]:
  wf_function fn /\ all_reachable fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETPC_PARAM /\ fn_inst_wf fn /\
  fn_defs_reach_uses fn /\
  (!i. MEM i (fn_insts fn) ==> ~MEM runner i.inst_outputs) ==>
  ~MEM runner (live_vars_at (liveness_analyze fn) s.vs_current_bb
    (SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `fn_reachable fn s.vs_current_bb` by
    (gvs[all_reachable_def, active_inst_def] >> metis_tac[]) >>
  gvs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  `LENGTH (collect_phis bb.bb_instructions) <= s.vs_inst_idx` by
    (spose_not_then assume_tac >>
     `s.vs_inst_idx < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
     drule collect_phis_index >> gvs[]) >>
  irule fmp_retpc_fresh_runner_not_live >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem fmp_retpc_covers[local]:
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_outputs = [pc] /\
  fmp_frame_covers sm env eb lo G ==>
  fmp_frame_covers sm env eb lo (step_prov PG G inst s1)
Proof
  strip_tac >> drule_all fmp_retpc_prov >>
  disch_then (qspecl_then [`s1`, `PG`, `G`] assume_tac) >>
  gvs[fmp_frame_covers_def, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem fmp_retpc_frame_preserves:
  wf_function fn /\ all_reachable fn /\ fn_inst_wf fn /\
  fn_defs_reach_uses fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [pc] /\ retpc_var fn pc /\
  (root <> NONE ==> !i. MEM i (fn_insts fn) ==> ~MEM runner i.inst_outputs) /\
  fmp_sites_ok sm fmp0 raw0 lo s.vs_fmp /\
  plan = fmp_stage_plan infos ctx fn /\
  root = fmp_stage_root infos ctx fn /\
  insts = (case lookup_block s.vs_current_bb fn.fn_blocks of
             SOME bb => bb.bb_instructions | NONE => []) /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  t.vs_inst_idx = fmp_stage_tidx plan root s.vs_current_bb insts s.vs_inst_idx /\
  fmp_env_rel sm fn (live_vars_at (liveness_analyze fn)
    s.vs_current_bb s.vs_inst_idx) G tn.t_var s t /\
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
  ((root = NONE /\
     t1 = update_var pc t.vs_return_pc_token t with vs_inst_idx := ti) \/
   (root = SOME (s.vs_current_bb,SUC s.vs_inst_idx) /\ pc <> runner /\
     t1 = update_var pc t.vs_return_pc_token
       (update_var runner (n2w lo) t) with vs_inst_idx := ti)) /\
  ti = fmp_stage_tidx plan root s.vs_current_bb insts (SUC s.vs_inst_idx) ==>
  fmp_frame_rel sm fmp0 raw0 eb elo lo F fn fn' PG
    (step_prov PG G inst s1) (step_taint inst s s1 tn).t_var
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1
Proof
  rpt strip_tac >>
  match_mp_tac (Q.INST [`tv` |-> `tn.t_var`] fmp_retpc_frame_reconstruct) >>
  simp[] >>
  gvs[] >>
  rpt conj_tac
  >- metis_tac[]
  >- (qpat_x_assum `s.vs_current_bb = t.vs_current_bb`
        (fn th => fs[GSYM th]) >>
      irule fmp_retpc_env_step >> metis_tac[])
  >- gvs[update_var_def, fmp_params_rel_def]
  >- metis_tac[]
  >- (qpat_x_assum `s.vs_current_bb = t.vs_current_bb`
        (fn th => fs[GSYM th]) >>
      irule fmp_retpc_env_runner_step >> simp[] >>
      drule_all fmp_retpc_runner_dead >> metis_tac[])
  >- gvs[update_var_def, fmp_params_rel_def]
  >> rpt strip_tac >>
  qpat_x_assum `SOME _ = fmp_stage_root _ _ _` (fn th => fs[GSYM th]) >>
  gvs[fmp_ledger_ok_def]
  >- (gvs[active_inst_def] >>
      qpat_x_assum `bb.bb_label = t.vs_current_bb` (fn th => fs[GSYM th]) >>
      `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
        gvs[venomWfTheory.wf_function_def, fn_labels_def] >>
      drule (Q.INST [`inst` |-> `EL s.vs_inst_idx bb.bb_instructions`]
        fmp_retpc_analysis_suc) >> simp[] >>
      disch_then (qspecl_then [`st`, `s`, `s.vs_inst_idx`, `bb`] mp_tac) >>
      simp[])
  >- (irule fmp_retpc_covers >> metis_tac[])
  >> metis_tac[fmp_retpc_empty_link]
QED

Theorem fmp_retpc_stage_write[local]:
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
  s1 = update_var pc s.vs_return_pc_token s /\
  (t1 = update_var pc t.vs_return_pc_token t with vs_inst_idx := ti \/
   t1 = update_var pc t.vs_return_pc_token (update_var runner (n2w lo) t)
          with vs_inst_idx := ti) /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_frame_rel sm fmp0 raw0 (fmp_frame_base raw0 stk)
    (fmp_frame_lo fmp0 ts) lo F fn fn' PG (step_prov PG G inst s1)
    (step_taint inst s s1 tn).t_var
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) t1 ==>
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
    (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo t1 ts
Proof
  rpt strip_tac >>
  gvs[] >>
  gvs[fmp_retpc_taint] >>
  gvs[fmp_stage_rel_def, update_var_def,
      fmp_retpc_shared_write] >> metis_tac[]
QED

Theorem fmp_retpc_preserves:
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  eb = fmp_frame_base raw0 stk /\ elo = fmp_frame_lo fmp0 ts /\
  wf_function fn /\ all_reachable fn /\ fn_inst_wf fn /\
  fn_defs_reach_uses fn /\ active_inst fn inst s /\
  inst.inst_opcode = RETPC_PARAM /\ inst.inst_operands = [Lit idx] /\
  inst.inst_outputs = [pc] /\ retpc_var fn pc /\
  (root <> NONE ==> !i. MEM i (fn_insts fn) ==> ~MEM runner i.inst_outputs) /\
  plan = fmp_stage_plan infos ctx fn /\
  root = fmp_stage_root infos ctx fn /\
  insts = (case lookup_block s.vs_current_bb fn.fn_blocks of
             SOME bb => bb.bb_instructions | NONE => []) /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  t.vs_inst_idx = fmp_stage_tidx plan root s.vs_current_bb insts s.vs_inst_idx /\
  fmp_env_rel sm fn (live_vars_at (liveness_analyze fn)
    s.vs_current_bb s.vs_inst_idx) G tn.t_var s t /\
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
  ((root = NONE /\
     t1 = update_var pc t.vs_return_pc_token t with vs_inst_idx := ti) \/
   (root = SOME (s.vs_current_bb,SUC s.vs_inst_idx) /\ pc <> runner /\
     t1 = update_var pc t.vs_return_pc_token
       (update_var runner (n2w lo) t) with vs_inst_idx := ti)) /\
  ti = fmp_stage_tidx plan root s.vs_current_bb insts (SUC s.vs_inst_idx) ==>
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
    (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo t1 ts
Proof
  rpt strip_tac >>
  match_mp_tac fmp_retpc_stage_write >>
  simp[] >>
  match_mp_tac fmp_retpc_frame_preserves >>
  simp[] >> gvs[fmp_stage_rel_def] >>
  TRY (qpat_x_assum `SOME _ = fmp_stage_root _ _ _`
    (fn th => gvs[GSYM th])) >>
  rpt strip_tac >>
  qpat_x_assum `!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==> _`
    (qspecl_then [`b`, `z`, `c`, `id`] mp_tac) >> simp[]
QED

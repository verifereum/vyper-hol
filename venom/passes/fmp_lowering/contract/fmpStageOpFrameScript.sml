(*
 * The stage relation after one ordinary instruction, rebuilt from the
 * local result fmpStageOpSimPure and fmpStageOpSimMem give: the frame moves to the next index
 * of its block with its runner, ledger and site map unchanged.
 *
 * TOP-LEVEL:
 *   fmp_stage_op_frame - the stage relation at the next index
 *)
Theory fmpStageOpFrame
Ancestors
  fmpStageControl fmpStageOpBase fmpStageReclaimSound fmpStageRel
  fmpLowerReclaimPlan fmpLedgerProps livenessProofs ptrDiscipline
  o1PassContract venomExecSemantics venomState venomInst
  decoderGhostFramePtr venomFnInstsProofs fmpStepAnalysis fmpStepStack
  list venomWf fmpReclaimDefs fmpAnalysisDefs fmpStepReclaim contextCodegenRel
  frameHistoryCfg simplifyCfgPhiSemantics venomWfProps

Theorem frame_reachable_dfs:
  EVERY wf_function C.ctx_functions /\
  frame_reachable vs C stk PG G tn fn inst s ==>
  MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  strip_tac >> drule_all frame_reachable_cfg_histories >> strip_tac >>
  drule frame_history_cfg_invariant >> simp[] >> strip_tac >>
  `wf_function fn` by gvs[EVERY_MEM] >>
  gvs[frame_history_cfg_def] >>
  irule fn_reachable_in_cfg_dfs_pre >> simp[] >>
  irule scfg_path_member_reachable >>
  qexists_tac `history_visits h` >>
  simp[] >> metis_tac[rich_listTheory.MEM_LAST_NOT_NIL]
QED

Theorem fmp_live_ordinary_suc:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb
    (SUC s.vs_inst_idx)) /\ ~MEM v inst.inst_outputs ==>
  MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `EVERY wf_function C.ctx_functions` by
    gvs[fmp_stage_ctx_def, o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  drule_all frame_reachable_dfs >> strip_tac >>
  `wf_function fn` by gvs[o1_fn_shape_def] >>
  gvs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[venomExecProofsTheory.wf_lookup_block] >>
  drule live_vars_at_propagate >> simp[inst_defs_def] >>
  disch_then irule >> simp[] >> metis_tac[]
QED

Theorem fmp_ordinary_not_reclaim[local]:
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA] ==>
  ~fmp_is_reclaim_point infos inst
Proof
  strip_tac >> spose_not_then assume_tac >>
  drule fmp_reclaim_point_opcodes >>
  gvs[] >> metis_tac[is_terminator_def]
QED

Theorem fmp_ordinary_analysis_suc[local]:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\ idx < LENGTH bb.bb_instructions /\
  inst = EL idx bb.bb_instructions /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; SETFMP] /\
  df_at NONE states bb.bb_label idx = SOME st ==>
  ?st'. df_at NONE states bb.bb_label (SUC idx) = SOME st' /\
    st'.frs_stack = st.frs_stack
Proof
  strip_tac >>
  `~fmp_is_reclaim_point infos inst` by
    (irule fmp_ordinary_not_reclaim >> gvs[]) >>
  `~fmp_clears_marks infos inst` by
    gvs[fmp_clears_marks_def, fmp_callee_info_def, fmp_invoke_target_def] >>
  drule_all fmp_reclaim_states_df_at_suc >>
  simp[fmp_transfer_def, fmp_reclaim_step_def, fmp_pop_at_def,
       fmp_apply_effect_def] >> gvs[]
QED

Theorem fmp_frame_covers_ordinary_step[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; PHI] /\
  step_inst k C inst s = OK s1 /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  fmp_frame_covers sm env (fmp_frame_base (w2n fmp) stk) lo G /\
  fmp_sites_ok sm fmp0 (w2n fmp) lo s.vs_fmp ==>
  fmp_frame_covers sm env (fmp_frame_base (w2n fmp) stk) lo
    (step_prov PG G inst s1)
Proof
  strip_tac >>
  drule_all fmp_stage_frame_facts >> strip_tac >>
  drule_all fmp_stage_frame_sites >> strip_tac >>
  irule fmp_stage_covers_step >>
  gvs[o1_fn_shape_def, fmp_sites_ok_def, EVERY_MEM] >>
  reverse (rpt conj_tac)
  >- (qexistsl_tac [`C`, `P`, `fn`, `k`, `s`] >> simp[]) 
  >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  metis_tac[]
QED

Theorem fmp_ordinary_root_boundary[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  MEM fn C.ctx_functions /\ o1_fn_shape C fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  active_inst fn inst s /\ inst.inst_opcode <> RETPC_PARAM ==>
  !rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
    s.vs_current_bb = rl ==> rp <> SUC s.vs_inst_idx
Proof
  rpt strip_tac >>
  drule_all fmp_stage_witness_pin >> strip_tac >>
  gvs[active_inst_def] >>
  `fn_is_context_entry ctx fn ==> entry_fn_no_params fn` by
    gvs[o1_fn_shape_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[venomExecProofsTheory.wf_lookup_block, o1_fn_shape_def] >>
  metis_tac[fmp_stage_root_crossing]
QED

Theorem fmp_ledger_step_frame[local]:
  ssa_form fn /\ MEM inst (fn_insts fn) /\ inst.inst_opcode <> DALLOCA /\
  fmp_reclaim_states infos fn = SOME states /\
  df_at NONE states lbl idx = SOME st /\
  MAP (\r. r.fr_mark) regions = st.frs_stack /\
  fmp_ledger_ok (fn_insts fn) env t lo regions /\
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) ==>
  fmp_ledger_ok (fn_insts fn) env (t1 with vs_inst_idx := j) lo regions
Proof
  strip_tac >> irule fmp_ledger_frame >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >>
  `EVERY (fmp_dalloca_output fn) st.frs_stack` by
    metis_tac[fmp_reclaim_states_stack] >>
  `fmp_dalloca_output fn r.fr_mark` by
    (`MEM r.fr_mark (MAP (\r. r.fr_mark) regions)` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     gvs[EVERY_MEM]) >>
  `~MEM r.fr_mark inst.inst_outputs` by
    (gvs[fmp_dalloca_output_def, ssa_form_def] >>
     metis_tac[all_distinct_flat_map_unique]) >>
  simp[lookup_var_def]
QED

Theorem fmp_env_rel_step[local]:
  fmp_env_rel sm fn live G tn.t_var s t /\
  (!v. MEM v live' /\ ~MEM v inst.inst_outputs ==> MEM v live) /\
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
    FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
    ?y. FLOOKUP t1.vs_vars v = SOME y /\
      (~retpc_var fn v ==> fmp_value_rel sm
        (FLOOKUP (step_prov PG G inst s1) v)
        (op_taint (step_taint inst s s1 tn) (Var v)) x y)) ==>
  fmp_env_rel sm fn live' (step_prov PG G inst s1)
    (step_taint inst s s1 tn).t_var
    (s1 with vs_inst_idx := i) (t1 with vs_inst_idx := j)
Proof
  simp[fmp_env_rel_def] >> rpt strip_tac >>
  Cases_on `MEM v inst.inst_outputs`
  >- (gvs[op_taint_def] >> metis_tac[]) >>
  `FLOOKUP (step_prov PG G inst s1) v = FLOOKUP G v` by
    simp[step_prov_other_output] >>
  `op_taint (step_taint inst s s1 tn) (Var v) = op_taint tn (Var v)` by
    simp[step_taint_other_output] >>
  gvs[op_taint_def] >> metis_tac[]
QED

Theorem fmp_ordinary_control_suc[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  MEM fn C.ctx_functions /\ o1_fn_shape C fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM] ==>
  fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
    s.vs_current_bb
    (case lookup_block s.vs_current_bb fn.fn_blocks of
       NONE => [] | SOME bb => bb.bb_instructions) (SUC s.vs_inst_idx) =
  SUC (fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
    s.vs_current_bb
    (case lookup_block s.vs_current_bb fn.fn_blocks of
       NONE => [] | SOME bb => bb.bb_instructions) s.vs_inst_idx)
Proof
  strip_tac >> fs[] >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
      s.vs_current_bb = rl ==> rp <> SUC s.vs_inst_idx` by
    metis_tac[fmp_ordinary_root_boundary] >>
  gvs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    metis_tac[venomExecProofsTheory.wf_lookup_block, o1_fn_shape_def] >>
  simp[] >> irule fmp_stage_tidx_suc >> simp[] >>
  spose_not_then assume_tac >>
  drule_all fmp_stage_plan_point >> strip_tac >>
  gvs[fmp_ordinary_not_reclaim]
QED

Theorem fmp_ordinary_root_transport[local]:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  step_inst k C inst s = OK s1 /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  fmp_stage_lowered infos ctx runner fn fn' /\
  fmp_stage_root infos ctx fn = SOME (rl,rp) /\
  fmp_sites_ok sm fmp0 (w2n fmp) lo s.vs_fmp /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  fmp_reclaim_states infos fn = SOME states /\
  df_at NONE states s.vs_current_bb s.vs_inst_idx = SOME st /\
  fmp_frame_covers sm env (fmp_frame_base (w2n fmp) stk) lo G /\
  (if s.vs_current_bb = rl /\ s.vs_inst_idx < rp then
     lo = fmp_frame_lo fmp0 ts /\ st.frs_stack = [] /\
     (fn_is_context_entry ctx fn ==> fmp0 = fmp_frame_lo fmp0 ts) /\
     (~fn_is_context_entry ctx fn ==>
       LENGTH s.vs_params = LENGTH (fn_user_param_insts fn) /\
       LENGTH s.vs_params < LENGTH t.vs_params /\
       EL (LENGTH s.vs_params) t.vs_params = n2w (fmp_frame_lo fmp0 ts))
   else lookup_var runner t = SOME (n2w lo) /\
     ?regions. fmp_ledger_ok (fn_insts fn) env t lo regions /\
       MAP (\r. r.fr_mark) regions = st.frs_stack /\
       EVERY (\r. fmp_frame_lo fmp0 ts <= r.fr_lo) regions /\
       fmp_ledger_link sm (fmp_frame_base (w2n fmp) stk) lo regions) /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_params = s.vs_params /\
  t1.vs_params = t.vs_params /\
  (!v. ~MEM v inst.inst_outputs ==>
    FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) ==>
  ?st'. df_at NONE states s1.vs_current_bb (SUC s.vs_inst_idx) = SOME st' /\
    fmp_frame_covers sm env (fmp_frame_base (w2n fmp) stk) lo
      (step_prov PG G inst s1) /\
    (if s1.vs_current_bb = rl /\ SUC s.vs_inst_idx < rp then
       lo = fmp_frame_lo fmp0 ts /\ st'.frs_stack = [] /\
       (fn_is_context_entry ctx fn ==> fmp0 = fmp_frame_lo fmp0 ts) /\
       (~fn_is_context_entry ctx fn ==>
         LENGTH s1.vs_params = LENGTH (fn_user_param_insts fn) /\
         LENGTH s1.vs_params < LENGTH t1.vs_params /\
         EL (LENGTH s1.vs_params) t1.vs_params = n2w (fmp_frame_lo fmp0 ts))
     else lookup_var runner (t1 with vs_inst_idx := j) = SOME (n2w lo) /\
       ?regions. fmp_ledger_ok (fn_insts fn) env
           (t1 with vs_inst_idx := j) lo regions /\
         MAP (\r. r.fr_mark) regions = st'.frs_stack /\
         EVERY (\r. fmp_frame_lo fmp0 ts <= r.fr_lo) regions /\
         fmp_ledger_link sm (fmp_frame_base (w2n fmp) stk) lo regions)
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >> fs[] >>
  `!rl rp. fmp_stage_root infos ctx fn = SOME (rl,rp) /\
      s.vs_current_bb = rl ==> rp <> SUC s.vs_inst_idx` by
    metis_tac[fmp_ordinary_root_boundary] >>
  `s.vs_current_bb = rl /\ SUC s.vs_inst_idx < rp <=>
    s.vs_current_bb = rl /\ s.vs_inst_idx < rp` by metis_tac[DECIDE ``a <> SUC b ==> (SUC b < a <=> b < a)``] >>
  `fmp_frame_covers sm env (fmp_frame_base (w2n fmp) stk) lo
      (step_prov PG G inst s1)` by
    (irule fmp_frame_covers_ordinary_step >> simp[] >> metis_tac[]) >>
  `?st'. df_at NONE states s.vs_current_bb (SUC s.vs_inst_idx) = SOME st' /\
      st'.frs_stack = st.frs_stack` by
    (gvs[active_inst_def] >>
     qpat_x_assum `bb.bb_label = s.vs_current_bb` (SUBST_ALL_TAC o SYM) >>
     irule fmp_ordinary_analysis_suc >>
     gvs[o1_fn_shape_def, wf_function_def, fn_labels_def,
         pre_fmp_ops_def, EVERY_MEM, pre_fmp_opcode_def] >>
     metis_tac[]) >>
  qexists_tac `st'` >> simp[] >>
  Cases_on `s.vs_current_bb = rl /\ s.vs_inst_idx < rp`
  >- gvs[] >>
  gvs[] >> IF_CASES_TAC >- metis_tac[] >> conj_tac
  >- (drule_all fmp_stage_witness_pin >> strip_tac >>
      gvs[lookup_var_def] >> metis_tac[]) >>
  qexists_tac `regions` >> simp[] >>
  irule fmp_ledger_step_frame >> metis_tac[]
QED

(* Why: an ordinary instruction is no reclaim point and changes no
   analysis stack, so the next index has no restore and the same stack;
   the control map moves by one (no DALLOCA, and the only step reaching
   the root is RETPC_PARAM, by fmp_stage_root_crossing and
   fmp_stage_witness_pin); variables live after it were live before it
   or are its outputs (live_vars_at_propagate); its outputs are neither
   the runner (fmp_stage_witness_pin) nor a ledger mark, a DALLOCA's
   output (ssa_form); and coverage carries over (fmp_stage_covers_step). *)
Theorem fmp_stage_op_frame:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  fmp0 = w2n vs'.vs_initial_fmp /\ raw0 = w2n fmp /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  ~s.vs_halted /\ ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; RETPC_PARAM; PHI] /\
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG G tn fn s lo t ts /\
  step_inst k C inst s = OK s1 /\
  (!v. ~MEM v inst.inst_outputs ==>
       FLOOKUP s1.vs_vars v = FLOOKUP s.vs_vars v /\
       FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v) /\
  (!v x. MEM v inst.inst_outputs /\ FLOOKUP s1.vs_vars v = SOME x ==>
     ?y. FLOOKUP t1.vs_vars v = SOME y /\
         (~retpc_var fn v ==>
          fmp_value_rel sm (FLOOKUP (step_prov PG G inst s1) v)
            (op_taint (step_taint inst s s1 tn) (Var v)) x y)) /\
  ld_memory_agree (fmp_ld_sites sm) eom
    (step_taint inst s s1 tn).t_mem s1.vs_memory t1.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address
    (step_taint inst s s1 tn) s1 t1 /\
  s1.vs_returndata = t1.vs_returndata /\
  ~s1.vs_halted /\ ~t1.vs_halted /\
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_prev_bb = s.vs_prev_bb /\
  s1.vs_inst_idx = s.vs_inst_idx /\ s1.vs_params = s.vs_params /\
  s1.vs_call_ctx = s.vs_call_ctx /\ s1.vs_tx_ctx = s.vs_tx_ctx /\
  s1.vs_block_ctx = s.vs_block_ctx /\
  s1.vs_data_section = s.vs_data_section /\
  s1.vs_labels = s.vs_labels /\ s1.vs_code = s.vs_code /\
  s1.vs_prev_hashes = s.vs_prev_hashes /\
  s1.vs_initial_fmp = s.vs_initial_fmp /\ s1.vs_fmp = s.vs_fmp /\
  t1.vs_current_bb = t.vs_current_bb /\ t1.vs_prev_bb = t.vs_prev_bb /\
  t1.vs_inst_idx = t.vs_inst_idx /\ t1.vs_params = t.vs_params /\
  t1.vs_call_ctx = t.vs_call_ctx /\ t1.vs_tx_ctx = t.vs_tx_ctx /\
  t1.vs_block_ctx = t.vs_block_ctx /\
  t1.vs_data_section = t.vs_data_section /\
  t1.vs_labels = t.vs_labels /\ t1.vs_code = t.vs_code /\
  t1.vs_prev_hashes = t.vs_prev_hashes /\
  t1.vs_initial_fmp = t.vs_initial_fmp /\ t1.vs_fmp = t.vs_fmp ==>
  fmp_stage_rel D C' sm fmp0 raw0 eom F stk PG
    (step_prov PG G inst s1) (step_taint inst s s1 tn) fn
    (s1 with vs_inst_idx := SUC s.vs_inst_idx) lo
    (t1 with vs_inst_idx := SUC t.vs_inst_idx) ts
Proof
  strip_tac >> drule_all fmp_stage_frame_facts >> strip_tac >>
  `!v. MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb
      (SUC s.vs_inst_idx)) /\ ~MEM v inst.inst_outputs ==>
      MEM v (live_vars_at (liveness_analyze fn) s.vs_current_bb s.vs_inst_idx)` by
    metis_tac[fmp_live_ordinary_suc] >>
  fs[fmp_stage_rel_def] >>
  reverse (rpt conj_tac)
  >- gvs[o1LowerDloadSharedTheory.ld_shared_agree_def]
  >- (fs[fmp_frame_rel_def] >>
      qexistsl_tac [`infos`, `ctx`, `runner`] >>
      `fmp_stage_tidx (fmp_stage_plan infos ctx fn) (fmp_stage_root infos ctx fn)
        s.vs_current_bb (case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => [] | SOME bb => bb.bb_instructions) (SUC s.vs_inst_idx) =
        SUC t.vs_inst_idx` by
        (drule_all (SRULE [] fmp_ordinary_control_suc) >> simp[] >> metis_tac[]) >>
      `fmp_env_rel sm fn
        (live_vars_at (liveness_analyze fn) s.vs_current_bb (SUC s.vs_inst_idx))
        (step_prov PG G inst s1) (step_taint inst s s1 tn).t_var
        (s1 with vs_inst_idx := SUC s.vs_inst_idx)
        (t1 with vs_inst_idx := SUC t.vs_inst_idx)` by
        (irule fmp_env_rel_step >> metis_tac[]) >>
      gvs[fmp_params_rel_def] >> conj_tac >- metis_tac[] >>
      qpat_x_assum `s.vs_current_bb = t.vs_current_bb` (SUBST_ALL_TAC o SYM) >>
      Cases_on `fmp_stage_root infos ctx fn` >- gvs[] >>
      PairCases_on `x` >> fs[] >>
      `!v. ~MEM v inst.inst_outputs ==>
        FLOOKUP t1.vs_vars v = FLOOKUP t.vs_vars v` by metis_tac[] >>
      drule_all (SRULE [] fmp_ordinary_root_transport) >>
      disch_then (qspec_then `SUC t.vs_inst_idx` strip_assume_tac) >>
      gvs[]) >>
  gvs[]
QED

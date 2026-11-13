Theory concretizeAnalysisReverseCoverage
Ancestors venomWfProps
  concretizeAnalysisChronologicalReady concretizeAnalysisReverseTransfer
  frameOriginHistoryCompletedWrites frameOriginHistory
  concretizePtrParamSupport frameOriginReachable
  concretizeAnalysisExclusiveWriters frameCfgBoundary contextCodegenRel
  frameHistoryCfg frameHistoryDefinitions removeUnusedSsaProofs venomExecProofs venomInst
  venomWf venomExecSemantics list

Theorem joint_origin_history_exclusive_ready:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx /\
  inst.inst_opcode <> PHI /\
  origin_reverse_covered P fn (origin_completed_writes h) om ==>
  origin_exclusive_ready P fn inst om
Proof
  strip_tac >> irule origin_exclusive_ready_covered >>
  goal_assum (drule_at Any) >> rpt strip_tac >>
  drule joint_origin_history_ordinary_completed_write >> simp[] >>
  disch_then irule >> simp[]
QED

Theorem eval_phis_prefix_resolves[local]:
  !is s post i. eval_phis s is = OK post /\
    MEM i (origin_phi_prefix is) ==>
    ?lbl op. s.vs_prev_bb = SOME lbl /\
      resolve_phi lbl i.inst_operands = SOME op
Proof
  Induct >> simp[origin_phi_prefix_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  simp[eval_phis_def, AllCaseEqs()] >> rpt strip_tac
  >- (gvs[eval_one_phi_def, AllCaseEqs()] >> metis_tac[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem joint_origin_history_phi_ready:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx /\
  ssa_form fn /\ fn_inst_wf fn /\ fn_ptr_ok P fn /\
  is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK post /\
  ~post.vs_halted /\ enters_block fn post t /\
  lookup_block post.vs_current_bb fn.fn_blocks = SOME bb /\
  origin_reverse_covered P fn (origin_completed_writes h) om ==>
  origin_phi_ready P fn s.vs_current_bb om bb.bb_instructions
Proof
  strip_tac >> drule joint_origin_history_projection >> strip_tac >>
  drule_all frame_history_cfg_invariant >> strip_tac >>
  `wf_function fn` by metis_tac[EVERY_MEM] >>
  drule frame_history_active >> strip_tac >>
  drule_all active_terminator_cfg_transition >> strip_tac >>
  drule enters_block_control_labels >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = t.vs_current_bb` by
    (conj_tac >- (gvs[lookup_block_def] >> metis_tac[venomExecProofsTheory.FIND_MEM]) >>
     metis_tac[lookup_block_label]) >>
  `?sp. eval_phis post bb.bb_instructions = OK sp` by
    gvs[enters_block_def] >>
  irule origin_phi_ready_covered >> goal_assum (drule_at Any) >>
  rpt strip_tac >>
  `?lbl op. post.vs_prev_bb = SOME lbl /\
     resolve_phi lbl i.inst_operands = SOME op` by
    metis_tac[eval_phis_prefix_resolves] >>
  `i.inst_opcode = PHI /\ MEM i bb.bb_instructions` by
    metis_tac[origin_phi_prefix_member] >>
  `MEM i (fn_insts fn)` by
    (gvs[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `?u. op = Var u /\ allocation_exclusive P fn u` by
    metis_tac[allocation_exclusive_phi_source] >> gvs[] >>
  drule joint_origin_history_phi_prefix_completed_write >> simp[] >>
  disch_then irule >> metis_tac[]
QED

Theorem successful_step_not_phi[local]:
  step_inst fuel ctx inst s = OK post ==> inst.inst_opcode <> PHI
Proof
  strip_tac >> strip_tac >> gvs[Once step_inst_def, step_inst_base_def]
QED

Theorem joint_origin_history_static_support:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions ==>
  MEM fn ctx.ctx_functions /\
  (!v p. FLOOKUP om v = SOME p ==> v IN fn_pv P fn)
Proof
  strip_tac >> drule joint_origin_history_erasure >> strip_tac >>
  drule origin_frame_erasure >> strip_tac >>
  `EVERY (\f. EVERY inst_wf (fn_insts f)) ctx.ctx_functions` by
    (gvs[EVERY_MEM, fn_inst_wf_def, fn_insts_def, fn_insts_blocks_flat,
         MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  drule_all ptr_frame_current_static >> strip_tac >> simp[] >>
  drule origin_frame_current_map >> strip_tac >>
  rpt strip_tac >>
  gvs[ptr_static_support_def] >>
  first_x_assum irule >>
  gvs[frameOriginUpdatesTheory.origin_erase_lookup] >>
  Cases_on `p` >> simp[] >> metis_tac[]
QED

Theorem joint_origin_history_reverse_coverage:
  !vs0 ctx stk PG G tn fn inst s oms om hs h.
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h ==>
  !P. EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx ==>
  origin_reverse_covered P fn (origin_completed_writes h) om /\
  LIST_REL (\f p. origin_reverse_covered P f.cf_fn
    (origin_completed_writes (SND p)) (FST p)) stk (ZIP (oms,hs))
Proof
  ho_match_mp_tac joint_origin_history_strongind >> rpt conj_tac
  >- simp[]
  >- suspend "ordinary"
  >- suspend "block"
  >- (rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      first_x_assum (qspec_then `P` mp_tac) >> simp[])
  >> suspend "return"
QED

Resume joint_origin_history_reverse_coverage[ordinary]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  drule joint_origin_history_endpoints >> strip_tac >>
  qmatch_goalsub_abbrev_tac `OriginObserve dst` >>
  drule origin_completed_writes_append >>
  disch_then (qspecl_then [`OriginOrdinary fuel s'`, `dst`,
                           `OriginSnapshot fn PG G om inst s`] mp_tac) >>
  simp[frameOriginHistoryPreservationTheory.origin_edge_writes_def] >>
  disch_then (fn th => rewrite_tac[th]) >>
  drule_all joint_origin_history_static_support >> strip_tac >>
  `inst.inst_opcode <> PHI` by metis_tac[successful_step_not_phi] >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `origin_exclusive_ready P fn inst om` by
    (drule joint_origin_history_exclusive_ready >> simp[] >>
     disch_then (qspec_then `P` irule) >> simp[]) >>
  irule origin_reverse_step >> simp[] >> metis_tac[EVERY_MEM]
QED
Resume joint_origin_history_reverse_coverage[block]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  drule joint_origin_history_endpoints >> strip_tac >>
  qmatch_goalsub_abbrev_tac `OriginObserve dst` >>
  drule origin_completed_writes_append >>
  disch_then (qspecl_then [`OriginBlock fuel s'`, `dst`,
                           `OriginSnapshot fn PG G om inst s`] mp_tac) >>
  simp[frameOriginHistoryPreservationTheory.origin_edge_writes_def] >>
  disch_then (fn th => rewrite_tac[th]) >>
  drule_all joint_origin_history_static_support >> strip_tac >>
  `wf_function fn /\ ssa_form fn /\ fn_inst_wf fn /\ fn_ptr_ok P fn` by
    metis_tac[EVERY_MEM] >>
  drule_all active_terminator_cfg_transition >> strip_tac >>
  drule enters_block_control_labels >> strip_tac >>
  `?bb. lookup_block s'.vs_current_bb fn.fn_blocks = SOME bb` by
    gvs[enters_block_def] >>
  `MEM bb fn.fn_blocks` by
    (gvs[lookup_block_def] >> metis_tac[venomExecProofsTheory.FIND_MEM]) >>
  `origin_phi_ready P fn s.vs_current_bb om bb.bb_instructions` by
    (drule joint_origin_history_phi_ready >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  simp[frameOriginHistoryPreservationTheory.origin_entry_writes_def,
       frameOriginUpdatesTheory.origin_entry_def] >>
  `s'.vs_prev_bb = SOME s.vs_current_bb` by metis_tac[] >>
  simp[] >> irule origin_reverse_phi_batch >> simp[]
QED
Resume joint_origin_history_reverse_coverage[return]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum (qspec_then `P` mp_tac) >> simp[] >> strip_tac >>
  drule joint_origin_history_endpoints >> simp[] >> strip_tac >>
  qmatch_goalsub_abbrev_tac `OriginObserve dst` >>
  rename1 `step_inst fuel ctx rinst s = IntRet ret s_end` >>
  qpat_x_assum `LAST h = _` kall_tac >>
  drule_at (Pat `LAST _ = _`) origin_completed_writes_append >>
  disch_then (qspecl_then [`OriginResume fuel fn rinst s ret s_end s'`, `dst`] mp_tac) >>
  simp[frameOriginHistoryPreservationTheory.origin_edge_writes_def] >>
  disch_then (fn th => rewrite_tac[th]) >>
  drule joint_origin_history_projection >> strip_tac >>
  drule_all frame_history_cfg_invariant >> simp[] >> strip_tac >>
  `MEM f.cf_inst (fn_insts f.cf_fn)` by
    (`origin_log ctx caller_h` by
       (drule joint_origin_history_saved_log >>
        disch_then (qspec_then `0` mp_tac) >> simp[]) >>
     drule origin_log_endpoint_active >>
     disch_then drule >> strip_tac >>
     gvs[active_inst_def, fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  irule origin_reverse_resume >> simp[] >> metis_tac[EVERY_MEM]
QED
Finalise joint_origin_history_reverse_coverage

Theorem joint_origin_history_current_reverse_coverage:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx ==>
  origin_reverse_covered P fn (origin_completed_writes h) om
Proof
  strip_tac >> drule joint_origin_history_reverse_coverage >>
  disch_then (qspec_then `P` mp_tac) >> simp[]
QED

Theorem joint_origin_history_saved_reverse_coverage:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx ==>
  LIST_REL (\f p. origin_reverse_covered P f.cf_fn
    (origin_completed_writes (SND p)) (FST p)) stk (ZIP (oms,hs))
Proof
  strip_tac >> drule joint_origin_history_reverse_coverage >>
  disch_then (qspec_then `P` mp_tac) >> simp[]
QED

Theorem joint_origin_history_ordinary_local_origin:
  joint_origin_history vs0 ctx stk PG G tn fn inst s oms om hs h /\
  EVERY (fn_ptr_ok P) ctx.ctx_functions /\
  EVERY wf_function ctx.ctx_functions /\ EVERY fn_inst_wf ctx.ctx_functions /\
  EVERY ssa_form ctx.ctx_functions /\
  EVERY fn_defs_reach_uses ctx.ctx_functions /\ ctx_inst_ids_distinct ctx /\
  inst.inst_opcode <> PHI /\ MEM (Var v) inst.inst_operands /\
  allocation_exclusive P fn v ==>
  ?aid site. FLOOKUP om v = SOME (OriginLocal aid,site)
Proof
  strip_tac >>
  `origin_reverse_covered P fn (origin_completed_writes h) om` by
    (drule joint_origin_history_current_reverse_coverage >> simp[] >>
     disch_then (qspec_then `P` irule) >> simp[]) >>
  `v IN origin_completed_writes h` by
    (drule joint_origin_history_ordinary_completed_write >> simp[]) >>
  drule_all origin_reverse_covered_lookup >> simp[]
QED

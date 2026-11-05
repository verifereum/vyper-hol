(* Cross-context rooted prefixes for bypass. *)
Theory simplifyCfgBypassPrefix
Ancestors
  simplifyCfgBypassRuns simplifyCfgBypassRootedEntry simplifyCfgEndpoints
  simplifyCfgBypassEntry simplifyCfgBypassShape simplifyCfgBypassPrecondition
  simplifyCfgBypassClosure simplifyCfgStaticInterface simplifyCfgFragments
  simplifyCfgBypassExec simplifyCfgFixupStatic simplifyCfgFramePrefixes
  simplifyCfgControl venomExecProps venomExecSemantics venomExecProofs
  venomInst venomState venomWf o1PassLift list cfgTransform simplifyCfgDefs contextCodegenRel

Theorem scfg_bypass_terminator_context_back:
  scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  frame_reach C fn s0 i s /\ is_terminator i.inst_opcode /\
  scfg_bypass_aligned a b s t /\
  step_inst k C'
    (scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) s.vs_current_bb i) t = OK v /\
  ~v.vs_halted ==>
  ?u w. step_inst k C i s = OK u /\ ~u.vs_halted /\ scfg_bprefix C fn u w /\
    scfg_bypass_aligned a b w v
Proof
  strip_tac >>
  `is_terminator (scfg_bypass_image a.bb_label b.bb_label
     (HD (bb_succs b)) s.vs_current_bb i).inst_opcode` by
    metis_tac[scfg_bypass_image_opcode, is_terminator_def] >>
  `(scfg_bypass_image a.bb_label b.bb_label
     (HD (bb_succs b)) s.vs_current_bb i).inst_opcode <> INVOKE` by
    (Cases_on `(scfg_bypass_image a.bb_label b.bb_label
       (HD (bb_succs b)) s.vs_current_bb i).inst_opcode` >> fs[is_terminator_def]) >>
  drule step_inst_ctx_irrel >>
  disch_then (qspecl_then [`k`, `C'`, `C`, `t`] assume_tac) >>
  irule scfg_bypass_terminator_back >> metis_tac[]
QED

Theorem scfg_bypass_exec_context_back:
  ctx_bisim C C' /\ scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  MEM bb fn.fn_blocks /\ bb.bb_label = s.vs_current_bb /\
  (!i. get_instruction bb s.vs_inst_idx = SOME i ==> frame_reach C fn s0 i s) /\
  phi_prefix_length (scfg_bypass_block a b bb).bb_instructions <= t.vs_inst_idx /\
  scfg_bypass_aligned a b s t /\
  exec_block k' C' (scfg_bypass_block a b bb) t = OK v /\ ~v.vs_halted ==>
  ?k u w. exec_block k C bb s = OK u /\
    scfg_bprefix C fn u w /\ scfg_bypass_aligned a b w v
Proof
  strip_tac >>
  drule scfg_exec_endpoint >> simp[] >> strip_tac >>
  rename1 `step_inst _ _ _ _ = OK v1` >>
  Cases_on `v1.vs_halted` >> gvs[] >>
  `bb_well_formed (scfg_bypass_block a b bb)` by
    metis_tac[scfg_bypass_block_wf, scfg_bypass_old_static, scfg_static_wf,
      wf_function_bb_well_formed] >>
  `?old. scfg_iprefix C bb s old /\ scfg_bypass_aligned a b old u` by
    (irule scfg_bypass_iprefix_backward >> metis_tac[]) >>
  `?j. get_instruction bb old.vs_inst_idx = SOME j /\
    i = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) old.vs_current_bb j` by
    (fs[scfg_bypass_instruction, scfg_bypass_aligned_def, scfg_ctrl_def] >>
     metis_tac[scfg_iprefix_current_bb]) >>
  `is_terminator j.inst_opcode` by
    metis_tac[scfg_bypass_image_opcode, is_terminator_def] >>
  `frame_reach C fn s0 j old` by
    (irule scfg_iprefix_frame_reach >> metis_tac[]) >>
  gvs[] >> drule_all scfg_bypass_terminator_context_back >>
  disch_then (qx_choosel_then [`u1`, `w1`] strip_assume_tac) >>
  `?k. exec_block k C bb s = OK u1` by
    (irule scfg_exec_endpoint_reconstruct >> simp[] >>
     qexistsl_tac [`j`, `k'`, `old`] >> simp[]) >>
  metis_tac[]
QED

Theorem scfg_bypass_run_block_context_back:
  ctx_bisim C C' /\ scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 /\
  run_block k' C' (scfg_bypass_block a b bb) t = OK v /\ ~v.vs_halted ==>
  ?k u w. run_block k C bb s = OK u /\
    scfg_bprefix C fn u w /\ scfg_bypass_aligned a b w v
Proof
  strip_tac >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME (scfg_bypass_block a b bb)` by
    (drule scfg_bypass_lookup_eq >> disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  `!e. (OK v : exec_result) <> Error e` by simp[] >>
  drule_all scfg_run_block_entry >> simp[] >>
  disch_then (qx_choose_then `y` strip_assume_tac) >>
  drule_all scfg_bypass_rooted_entry_backward >>
  disch_then (qx_choose_then `x` strip_assume_tac) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `phi_prefix_length (scfg_bypass_block a b bb).bb_instructions <= y.vs_inst_idx` by simp[] >>
  drule_all scfg_bypass_exec_context_back >> strip_tac >>
  qpat_x_assum `enters_block fn' t y` kall_tac >>
  drule_all scfg_enters_block_run_block >>
  disch_then (qspecl_then [`k`, `C`] assume_tac) >>
  qexistsl_tac [`k`, `u`, `w`] >> simp[]
QED

Theorem scfg_bypass_bprefix_back:
  !C' fn' t v. scfg_bprefix C' fn' t v ==>
  !C fn a b s0 s. ctx_bisim C C' /\ scfg_bypass_hyp fn a b fn' /\
    fn_entry_state fn s0 /\ scfg_bprefix C fn s0 s /\
    scfg_bypass_aligned a b s t /\ s.vs_inst_idx = 0 ==>
    ?w. scfg_bprefix C fn s0 w /\ scfg_bypass_aligned a b w v
Proof
  ho_match_mp_tac scfg_bprefix_ind >> rpt strip_tac
  >- metis_tac[] >>
  `?oldbb. lookup_block s.vs_current_bb fn.fn_blocks = SOME oldbb /\
      bb = scfg_bypass_block a b oldbb` by
    (drule scfg_bypass_lookup_eq >>
     disch_then (qspec_then `t.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
     Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[]) >>
  gvs[] >> drule_all scfg_bypass_run_block_context_back >> strip_tac >>
  `scfg_bprefix C fn s0 w` by
    (irule scfg_bprefix_trans >> goal_assum (drule_at Any) >>
     irule scfg_bprefix_trans >> goal_assum (drule_at Any) >>
     irule scfg_bprefix_single >> metis_tac[run_block_OK_not_halted]) >>
  `w.vs_inst_idx = 0` by
    (qpat_assum `run_block _ C' _ _ = OK _`
       (mp_tac o MATCH_MP run_block_OK_inst_idx_0) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem scfg_bypass_rooted_observe:
  ctx_bisim C C' /\ scfg_bypass_hyp fn a b fn' /\ fn_entry_state fn s0 /\
  scfg_bypass_aligned a b s0 t0 /\ frame_reach C' fn' t0 j v ==>
  ?u i. frame_reach C fn s0 i u /\
    j = scfg_bypass_image a.bb_label b.bb_label (HD (bb_succs b)) u.vs_current_bb i /\
    scfg_bypass_aligned a b u v
Proof
  strip_tac >>
  `wf_function fn'` by
    metis_tac[scfg_bypass_normalized, scfg_normalized_static, scfg_static_wf] >>
  drule_all scfg_frame_reach_decompose >>
  disch_then (qx_choosel_then [`s`, `bb`, `v1`, `ent`] strip_assume_tac) >>
  `s0.vs_inst_idx = 0` by fs[fn_entry_state_def] >>
  `?w. scfg_bprefix C fn s0 w /\ scfg_bypass_aligned a b w s` by
    (irule scfg_bypass_bprefix_back >> simp[] >>
     metis_tac[scfg_bprefix_rules]) >>
  `w.vs_inst_idx = 0` by
    (qpat_assum `scfg_bprefix C fn s0 w` (mp_tac o MATCH_MP scfg_bprefix_last) >>
     metis_tac[run_block_OK_inst_idx_0]) >>
  `?bb0. lookup_block w.vs_current_bb fn.fn_blocks = SOME bb0 /\
      bb = scfg_bypass_block a b bb0` by
    (drule scfg_bypass_lookup_eq >>
     disch_then (qspec_then `s.vs_current_bb` mp_tac) >>
     fs[scfg_bypass_aligned_def, scfg_ctrl_def] >>
     Cases_on `lookup_block w.vs_current_bb fn.fn_blocks` >> gvs[]) >>
  `enters_block fn' s ent` by
    (simp[enters_block_def] >> metis_tac[]) >>
  drule_all scfg_bypass_rooted_entry_backward >>
  disch_then (qx_choose_then `x` strip_assume_tac) >>
  `MEM bb0 fn.fn_blocks` by metis_tac[lookup_block_member_label] >>
  `bb_well_formed (scfg_bypass_block a b bb0)` by
    metis_tac[scfg_bypass_block_wf, scfg_bypass_old_static, scfg_static_wf,
      wf_function_bb_well_formed] >>
  `phi_prefix_length (scfg_bypass_block a b bb0).bb_instructions <= ent.vs_inst_idx` by simp[] >>
  qpat_x_assum `bb = scfg_bypass_block _ _ _` SUBST_ALL_TAC >>
  drule_all scfg_bypass_iprefix_observe >> strip_tac >>
  qexistsl_tac [`u`, `i`] >> simp[] >>
  metis_tac[scfg_iprefix_current_bb]
QED

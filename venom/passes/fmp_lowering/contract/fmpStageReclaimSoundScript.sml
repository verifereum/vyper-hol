(*
 * Reclaim soundness for FmpLowering's stage simulation: the facts about
 * the source run and the reclaim analysis that let a restore drop sites
 * no live pointer uses.
 *
 * TOP-LEVEL:
 *   fmp_stage_frame_sites    - a frame_reachable state's sites lie between
 *                              fmp and its frontier, a frame's own above its
 *                              entry fmp and its parameters' below
 *   fmp_stage_covers_step    - an ordinary step keeps base coverage
 *   fmp_stage_covers_dalloca - a DALLOCA step keeps it, with its new site
 *   fmp_stage_covers_phis    - block entry keeps it
 *   fmp_stage_live_edge      - a variable live after a successor's PHIs is
 *                              its PHI operand's or live itself at the
 *                              predecessor's terminator
 *   fmp_stage_out_not_kept   - a DALLOCA's output is not on the analysis
 *                              stack before it
 *)
Theory fmpStageReclaimSound
Ancestors
  fmpStageRel ptrStaticDiscipline cfgWf venomWf livenessProofs
  fmpLowerReclaimPlan venomWfProps venomExecProofs removeUnusedProofs
  fnFrameSinglePred fmpReclaimDefs list arithmetic

Theorem fmp_stage_frame_sites:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s ==>
  w2n fmp <= fmp_frame_base (w2n fmp) stk /\
  fmp_frame_base (w2n fmp) stk <= w2n s.vs_fmp /\
  EVERY (\f. w2n f.cf_state.vs_fmp <= w2n s.vs_fmp) stk /\
  (!v b z. FLOOKUP G v = SOME (b,z) /\ 0 < z ==>
     w2n fmp <= b /\ b + z <= w2n s.vs_fmp) /\
  EVERY (\h. !b z. h = SOME (b,z) /\ 0 < z ==>
               b + z <= fmp_frame_base (w2n fmp) stk) PG
Proof
  cheat
QED

Theorem fmp_stage_covers_step:
  fmp_base_analyze (fn_insts fn) = SOME env /\ fn_static_ptr_ok P fn /\
  fn_inst_wf fn /\ EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  pre_fmp_ops fn /\
  wf_function fn /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\
  ~MEM inst.inst_opcode [INVOKE; DALLOCA; PHI] /\
  step_inst k C inst s = OK s1 /\
  fmp_frame_covers sm env eb lo G /\
  EVERY (\h. !b z. h = SOME (b,z) ==> b < eb) PG ==>
  fmp_frame_covers sm env eb lo (step_prov PG G inst s1)
Proof
  cheat
QED

Theorem fmp_stage_covers_dalloca:
  fmp_base_analyze (fn_insts fn) = SOME env /\ wf_function fn /\
  active_inst fn inst s /\ inst.inst_opcode = DALLOCA /\
  step_inst k C inst s = OK s1 /\
  fmp_frame_covers sm env eb lo G /\
  (!b z c id. FLOOKUP sm (b,z) = SOME (c,id) ==>
     0 < z /\ b + z <= w2n s.vs_fmp /\ c + z <= lo) /\
  (!v b z. FLOOKUP G v = SOME (b,z) /\ 0 < z ==> b + z <= w2n s.vs_fmp) ==>
  fmp_frame_covers
    (if w2n s1.vs_fmp = w2n s.vs_fmp then sm
     else sm |+ ((w2n s.vs_fmp, w2n s1.vs_fmp - w2n s.vs_fmp),
                (lo, inst.inst_id)))
    env eb (lo + (w2n s1.vs_fmp - w2n s.vs_fmp))
    (step_prov PG G inst s1)
Proof
  cheat
QED

Theorem fmp_stage_covers_phis:
  fmp_base_analyze (fn_insts fn) = SOME env /\ wf_function fn /\
  fmp_frame_covers sm env eb lo G /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  fmp_frame_covers sm env eb lo (entry_prov fn s G)
Proof
  cheat
QED

Theorem fmp_stage_live_edge:
  wf_function fn /\ fn_inst_wf fn /\
  fmp_reclaim_states infos fn = SOME states /\
  MEM pl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_succs_of (cfg_analyze fn) pl) /\
  lookup_block pl fn.fn_blocks = SOME pbb /\
  lookup_block sl fn.fn_blocks = SOME sbb /\
  pbb.bb_instructions <> [] /\
  MEM v (live_vars_at (liveness_analyze fn) sl
           (phi_prefix_length sbb.bb_instructions)) ==>
  (?phi. MEM phi (collect_phis sbb.bb_instructions) /\
         MEM v phi.inst_outputs /\
         !u. resolve_phi pl phi.inst_operands = SOME (Var u) ==>
             MEM u (live_vars_at (liveness_analyze fn) pl
                      (PRE (LENGTH pbb.bb_instructions)))) \/
  (MEM v (live_vars_at (liveness_analyze fn) pl
            (PRE (LENGTH pbb.bb_instructions))) /\
   EVERY (\q. ~MEM v q.inst_outputs) (collect_phis sbb.bb_instructions))
Proof
  cheat
QED

Theorem fresh_transfer[local]:
  ~MEM v inst.inst_outputs /\ ~MEM v st.frs_stack /\
  fmp_transfer infos fn live env p inst (SOME st) = SOME st' ==>
  ~MEM v st'.frs_stack
Proof
  strip_tac >>
  Cases_on `fmp_pop_at infos fn live env p inst st` >>
  rename1 `fmp_pop_at infos fn live env p inst st = (popped,kept)` >>
  drule fmp_pop_at_kept >> strip_tac >>
  gvs[fmp_transfer_def, fmp_reclaim_step_def] >>
  Cases_on `fmp_clears_marks infos inst` >>
  gvs[fmp_apply_effect_def, fmp_empty_reclaim_state_def] >>
  Cases_on `inst.inst_opcode = DALLOCA` >> gvs[] >>
  Cases_on `inst.inst_outputs` >>
  gvs[fmpAliasDefsTheory.fmp_single_output_def] >>
  rename1 `inst.inst_outputs = h::tail` >>
  Cases_on `tail` >> gvs[fmpAliasDefsTheory.fmp_single_output_def]
QED

Theorem fresh_block_prefix[local]:
  !n st. fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\ MEM bb fn.fn_blocks /\
  n <= LENGTH bb.bb_instructions /\
  (!j. j < n ==> ~MEM v (EL j bb.bb_instructions).inst_outputs) /\
  df_at NONE states bb.bb_label 0 = SOME start /\ ~MEM v start.frs_stack /\
  df_at NONE states bb.bb_label n = SOME st ==> ~MEM v st.frs_stack
Proof
  Induct >> rpt gen_tac >> strip_tac >- gvs[] >>
  `n < LENGTH bb.bb_instructions` by simp[] >>
  drule_all fmp_reclaim_states_df_at_suc >> strip_tac >>
  Cases_on `df_at NONE states bb.bb_label n`
  >- gvs[fmp_transfer_def, fmp_reclaim_step_def] >>
  rename1 `df_at NONE states bb.bb_label n = SOME prev` >>
  `~MEM v prev.frs_stack` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `~MEM v (EL n bb.bb_instructions).inst_outputs` by simp[] >>
  metis_tac[fresh_transfer]
QED

Theorem fresh_first_hit[local]:
  !R a b. RTC R a b ==> !P.
  P a /\ (!x y. R x y /\ x <> b /\ P x ==> P y) ==> P b
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >>
  rpt strip_tac >> metis_tac[]
QED

Theorem fresh_edge_step[local]:
  wf_function fn /\ ssa_form fn /\
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  MEM out (EL k bb.bb_instructions).inst_outputs /\
  (!pb n s. MEM pb fn.fn_blocks /\ n <= LENGTH pb.bb_instructions /\
    df_at NONE states pb.bb_label 0 = SOME s ==>
    ?t. df_at NONE states pb.bb_label n = SOME t) /\
  (!pb sb t. MEM pb fn.fn_blocks /\ MEM sb fn.fn_blocks /\
    MEM sb.bb_label (cfg_succs_of (cfg_analyze fn) pb.bb_label) /\
    df_at NONE states pb.bb_label (LENGTH pb.bb_instructions) = SOME t ==>
    ?s ks. df_at NONE states sb.bb_label 0 = SOME s /\
           t.frs_stack = s.frs_stack ++ ks) /\
  fn_cfg_edge fn a b /\ a <> bb.bb_label /\
  df_at NONE states a 0 = SOME start /\ ~MEM out start.frs_stack ==>
  ?s. df_at NONE states b 0 = SOME s /\ ~MEM out s.frs_stack
Proof
  strip_tac >>
  `?sb. lookup_block b fn.fn_blocks = SOME sb` by
    metis_tac[fn_cfg_edge_target_block] >>
  `MEM sb fn.fn_blocks /\ sb.bb_label = b` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM b (cfg_succs_of (cfg_analyze fn) a)` by
    metis_tac[fn_cfg_edge_succs] >>
  qpat_x_assum `fn_cfg_edge fn a b` mp_tac >>
  simp[fn_cfg_edge_def] >> strip_tac >>
  rename1 `MEM pb fn.fn_blocks` >>
  `?t. df_at NONE states pb.bb_label (LENGTH pb.bb_instructions) = SOME t` by
    metis_tac[LESS_EQ_REFL] >>
  `!j. j < LENGTH pb.bb_instructions ==>
       ~MEM out (EL j pb.bb_instructions).inst_outputs` by
    metis_tac[ssa_form_position] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, venomInstTheory.fn_labels_def] >>
  `~MEM out t.frs_stack` by
    (gvs[] >>
     `LENGTH pb.bb_instructions <= LENGTH pb.bb_instructions` by simp[] >>
     drule_all fresh_block_prefix >> simp[]) >>
  metis_tac[MEM_APPEND]
QED

Theorem fresh_out_conditional[local]:
  wf_function fn /\ ssa_form fn /\ all_reachable fn /\
  fmp_reclaim_states infos fn = SOME states /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = DALLOCA /\
  (EL k bb.bb_instructions).inst_outputs = [out] /\
  df_at NONE states bb.bb_label k = SOME st /\
  (!ebb. entry_block fn = SOME ebb ==>
    ?s. df_at NONE states ebb.bb_label 0 = SOME s /\ s.frs_stack = []) /\
  (!pb n s. MEM pb fn.fn_blocks /\ n <= LENGTH pb.bb_instructions /\
    df_at NONE states pb.bb_label 0 = SOME s ==>
    ?t. df_at NONE states pb.bb_label n = SOME t) /\
  (!pb sb t. MEM pb fn.fn_blocks /\ MEM sb fn.fn_blocks /\
    MEM sb.bb_label (cfg_succs_of (cfg_analyze fn) pb.bb_label) /\
    df_at NONE states pb.bb_label (LENGTH pb.bb_instructions) = SOME t ==>
    ?s ks. df_at NONE states sb.bb_label 0 = SOME s /\
           t.frs_stack = s.frs_stack ++ ks) ==>
  ~MEM out st.frs_stack
Proof
  strip_tac >>
  `?env. fmp_base_analyze (fn_insts fn) = SOME env` by
    metis_tac[fmpReclaimPropsTheory.fmp_reclaim_states_has_bases] >>
  `fn_reachable fn bb.bb_label` by metis_tac[all_reachable_def] >>
  gvs[fn_reachable_def] >>
  qpat_x_assum `fn_entry_label fn = SOME entry` mp_tac >>
  simp[venomInstTheory.fn_entry_label_def, AllCaseEqs()] >> strip_tac >>
  rename1 `entry_block fn = SOME ebb` >>
  `?start. df_at NONE states ebb.bb_label 0 = SOME start /\
           ~MEM out start.frs_stack` by metis_tac[MEM] >>
  `?s. df_at NONE states bb.bb_label 0 = SOME s /\ ~MEM out s.frs_stack` by
    (drule fresh_first_hit >>
     disch_then (qspec_then
       `\l. ?s. df_at NONE states l 0 = SOME s /\ ~MEM out s.frs_stack`
       (irule o BETA_RULE)) >>
     reverse conj_tac >- metis_tac[] >>
     rpt strip_tac >>
     `MEM out (EL k bb.bb_instructions).inst_outputs` by simp[] >>
     drule_all fresh_edge_step >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, venomInstTheory.fn_labels_def] >>
  `!j. j < k ==> ~MEM out (EL j bb.bb_instructions).inst_outputs` by
    (rpt strip_tac >>
     `j < LENGTH bb.bb_instructions` by simp[] >>
     `MEM out (EL k bb.bb_instructions).inst_outputs` by simp[] >>
     `j = k` by metis_tac[ssa_form_position] >> gvs[]) >>
  `k <= LENGTH bb.bb_instructions` by simp[] >>
  drule_all fresh_block_prefix >> simp[]
QED

Theorem fmp_stage_out_not_kept:
  wf_function fn /\ ssa_form fn /\ all_reachable fn /\
  fmp_reclaim_states infos fn = SOME states /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = DALLOCA /\
  (EL k bb.bb_instructions).inst_outputs = [out] /\
  df_at NONE states bb.bb_label k = SOME st ==>
  ~MEM out st.frs_stack
Proof
  cheat
QED

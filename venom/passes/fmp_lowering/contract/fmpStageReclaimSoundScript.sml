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
  fnBlockPlanStaticOffsetLive fnPlanLineageLiveness fnBlockPlanStatic
  fmpLowerReclaimPlan venomWfProps venomExecProofs removeUnusedProofs
  fnFrameSinglePred fmpReclaimDefs basePtrProofs venomInst list arithmetic
  fmpStageReclaimFresh

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

Theorem fmp_ready_nonphi_input[local]:
  wf_function fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  bb.bb_label = lbl /\ fmp_phi_ready_block (liveness_analyze fn) bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) /\
  EVERY (\q. ~MEM v q.inst_outputs) (collect_phis bb.bb_instructions) ==>
  MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))
Proof
  strip_tac >> irule input_vars_from_non_phi >> conj_tac
  >~ [`!inst. MEM inst (collect_phis bb.bb_instructions) ==> ~MEM v (MAP SND (phi_pairs inst.inst_operands))`]
  >- (gvs[fmp_phi_ready_block_def, EVERY_MEM, inst_uses_def] >>
      metis_tac[phi_pairs_mem_operand_vars]) >>
  drule live_vars_at_propagate_range >> simp[] >>
  disch_then irule >> simp[] >>
  qexists_tac `LENGTH (collect_phis bb.bb_instructions)` >>
  simp[current_collect_phis_length] >> rpt strip_tac >>
  drule collect_phis_index >> strip_tac >>
  gvs[EVERY_MEM, inst_defs_def] >> metis_tac[EL_MEM]
QED

Theorem fmp_input_at_terminator[local]:
  wf_function fn /\ fn_inst_wf fn /\
  MEM pl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_analyze fn).cfg_dfs_pre /\
  MEM sl (cfg_succs_of (cfg_analyze fn) pl) /\
  lookup_block pl fn.fn_blocks = SOME pbb /\
  lookup_block sl fn.fn_blocks = SOME sbb /\
  pbb.bb_instructions <> [] /\
  MEM x (input_vars_from pl sbb.bb_instructions
    (live_vars_at (liveness_analyze fn) sl 0)) ==>
  MEM x (live_vars_at (liveness_analyze fn) pl
    (PRE (LENGTH pbb.bb_instructions)))
Proof
  strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) pl` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `MEM x (live_vars_at (liveness_analyze fn) pl
     (LENGTH pbb.bb_instructions))` by
    (drule_all analyzed_live_out_edge_subset >>
     simp[pred_setTheory.SUBSET_DEF]) >>
  `MEM pbb fn.fn_blocks` by
    metis_tac[livenessTransferProofsTheory.lookup_block_mem] >>
  `bb_well_formed pbb` by gvs[wf_function_def] >>
  `inst_wf (LAST pbb.bb_instructions)` by
    metis_tac[fn_inst_wf_def, rich_listTheory.MEM_LAST_NOT_NIL] >>
  `(LAST pbb.bb_instructions).inst_outputs = []` by
    metis_tac[venomExecProofsTheory.terminator_no_outputs, bb_well_formed_def] >>
  drule live_vars_at_propagate >> simp[] >> disch_then irule >>
  `0 < LENGTH pbb.bb_instructions` by
    (Cases_on `pbb.bb_instructions` >> gvs[]) >>
  `SUC (PRE (LENGTH pbb.bb_instructions)) = LENGTH pbb.bb_instructions` by decide_tac >>
  simp[inst_defs_def, GSYM LAST_EL]
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

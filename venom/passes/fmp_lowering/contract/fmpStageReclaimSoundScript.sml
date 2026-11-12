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
  list venomInst fmpReclaimDefs venomExecSemantics dftCommutation
  livenessTransferProofs venomExecProofs While basePtrProofs
  fnBlockPlanStaticOffsetLive fnPlanLineageLiveness fnBlockPlanStatic

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

Theorem fmp_ready_phi_other_source[local]:
  fmp_phi_ready_block live bb /\
  MEM phi (collect_phis bb.bb_instructions) /\
  LENGTH phi.inst_outputs = 1 /\ MEM v phi.inst_outputs /\
  MEM v (live_vars_at live bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions))) /\
  MEM u (inst_uses phi) /\ u <> v ==>
  EVERY (\q. ~MEM u q.inst_outputs) (collect_phis bb.bb_instructions)
Proof
  strip_tac >>
  `phi.inst_outputs = [v]` by
    (Cases_on `phi.inst_outputs` >> gvs[] >>
     rename1 `LENGTH rest = 0` >> Cases_on `rest` >> gvs[]) >>
  gvs[fmp_phi_ready_block_def, EVERY_MEM] >>
  first_x_assum (qspec_then `phi` mp_tac) >> simp[] >>
  disch_then (qspec_then `u` mp_tac) >> simp[]
QED

Theorem fmp_ready_phi_earliest_source[local]:
  wf_function fn /\ fn_inst_wf fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  fmp_phi_ready_block (liveness_analyze fn) bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) /\
  j < LENGTH (collect_phis bb.bb_instructions) /\
  MEM v (EL j (collect_phis bb.bb_instructions)).inst_outputs /\
  (!k. k < j ==> ~MEM v (EL k (collect_phis bb.bb_instructions)).inst_outputs) /\
  resolve_phi pred (EL j (collect_phis bb.bb_instructions)).inst_operands = SOME (Var u) ==>
  MEM u (live_vars_at (liveness_analyze fn) lbl 0)
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `EL j (collect_phis bb.bb_instructions) = EL j bb.bb_instructions /\
   (EL j bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[collect_phis_index] >>
  `j < LENGTH bb.bb_instructions` by
    metis_tac[current_collect_phis_length, arithmeticTheory.LESS_LESS_EQ_TRANS] >>
  `MEM u (inst_uses (EL j bb.bb_instructions))` by
    metis_tac[resolve_phi_MEM, operand_var_in_inst_uses] >>
  `MEM u (live_vars_at (liveness_analyze fn) lbl j)` by
    (drule live_vars_at_uses >> simp[] >> disch_then irule >> metis_tac[]) >>
  `!k. k < j ==> ~MEM u (inst_defs (EL k bb.bb_instructions))` by
    (Cases_on `u = v`
     >- (gvs[inst_defs_def] >> rpt strip_tac >>
         `k < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
         metis_tac[collect_phis_index]) >>
     `inst_wf (EL j bb.bb_instructions)` by
       metis_tac[fn_inst_wf_def, lookup_block_mem, EL_MEM] >>
     `LENGTH (EL j bb.bb_instructions).inst_outputs = 1` by
       gvs[inst_wf_def] >>
     `EVERY (\q. ~MEM u q.inst_outputs) (collect_phis bb.bb_instructions)` by
       (irule fmp_ready_phi_other_source >> goal_assum (drule_at Any) >>
        qexistsl_tac [`liveness_analyze fn`, `v`] >> simp[] >> metis_tac[EL_MEM]) >>
     rpt strip_tac >>
     `k < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
     `EL k (collect_phis bb.bb_instructions) = EL k bb.bb_instructions` by
       metis_tac[collect_phis_index] >>
     `MEM (EL k bb.bb_instructions) (collect_phis bb.bb_instructions)` by
       metis_tac[EL_MEM] >>
     gvs[EVERY_MEM, inst_defs_def] >> metis_tac[]) >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >>
  simp[] >> qexists_tac `j` >> simp[]
QED

Theorem fmp_ready_phi_witness[local]:
  wf_function fn /\ fn_inst_wf fn /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  fmp_phi_ready_block (liveness_analyze fn) bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) /\
  (?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs) ==>
  ?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs /\
    !pred u. resolve_phi pred phi.inst_operands = SOME (Var u) ==>
      MEM u (live_vars_at (liveness_analyze fn) lbl 0)
Proof
  strip_tac >>
  `?j. j < LENGTH (collect_phis bb.bb_instructions) /\
       MEM v (EL j (collect_phis bb.bb_instructions)).inst_outputs` by
    metis_tac[MEM_EL] >>
  rename1 `j < LENGTH (collect_phis bb.bb_instructions)` >>
  `?m. (m < LENGTH (collect_phis bb.bb_instructions) /\
         MEM v (EL m (collect_phis bb.bb_instructions)).inst_outputs) /\
       !k. k < m ==> ~(k < LENGTH (collect_phis bb.bb_instructions) /\
         MEM v (EL k (collect_phis bb.bb_instructions)).inst_outputs)` by
    (ho_match_mp_tac arithmeticTheory.WOP >> qexists_tac `j` >> simp[]) >>
  qpat_x_assum `j < LENGTH _` kall_tac >>
  qpat_x_assum `MEM v (EL j _).inst_outputs` kall_tac >>
  rename1 `m < LENGTH (collect_phis bb.bb_instructions)` >>
  qexists_tac `EL m (collect_phis bb.bb_instructions)` >>
  simp[EL_MEM] >> rpt strip_tac >>
  irule fmp_ready_phi_earliest_source >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`m`, `pred`, `v`] >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[]
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
  >- (drule live_vars_at_propagate_range >> simp[] >>
      disch_then irule >>
      qexists_tac `LENGTH (collect_phis bb.bb_instructions)` >>
      simp[current_collect_phis_length] >> rpt strip_tac >>
      drule collect_phis_index >> strip_tac >>
      gvs[EVERY_MEM, inst_defs_def] >> metis_tac[EL_MEM]) >>
  gvs[fmp_phi_ready_block_def, EVERY_MEM, inst_uses_def] >>
  metis_tac[phi_pairs_mem_operand_vars]
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

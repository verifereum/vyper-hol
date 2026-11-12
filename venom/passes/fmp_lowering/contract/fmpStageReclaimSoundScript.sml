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
  pair list finite_map indexedLists livenessDefs venomInst fmpReclaimDefs basePtrProofs
  venomExecSemantics venomFnInstsProofs fnLineageStatic
  fmpLowerReclaimPlan venomWfProps venomExecProofs removeUnusedProofs
  fnFrameSinglePred arithmetic fmpStageReclaimFresh

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

(* First occurrence selection, without distinct predecessor labels. *)
Theorem fmp_resolve_find_pairs[local]:
  !ops pred. phi_well_formed ops ==>
    resolve_phi pred ops =
      case FIND (\(l,w). l = pred) (phi_pairs ops) of
        NONE => NONE | SOME (_,w) => SOME (Var w)
Proof
  ho_match_mp_tac venomInstTheory.phi_pairs_ind >>
  rw[phi_pairs_def, phi_well_formed_def, resolve_phi_def, FIND_thm] >> rw[]
QED

Theorem fmp_maps_fold_selected[local]:
  !items (om:string |-> num) (mm:num |-> string) pred v idx src.
    EVERY (\(i,phi).
      (MEM v (MAP SND (phi_pairs phi.inst_operands)) ==> i = idx) /\
      (i = idx ==> MEM v (MAP SND (phi_pairs phi.inst_operands)) /\
        FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) =
                    SOME (pred,src))) items /\
    (MEM idx (MAP FST items) \/
     (FLOOKUP om v = SOME idx /\ FLOOKUP mm idx = SOME src)) ==>
    FLOOKUP (FST (FOLDL (\(op_map,matching) (i,phi).
      (FOLDL (\m (l,w). m |+ (w,i)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,w) => matching |+ (i,w)))
      (om,mm) items)) v = SOME idx /\
    FLOOKUP (SND (FOLDL (\(op_map,matching) (i,phi).
      (FOLDL (\m (l,w). m |+ (w,i)) op_map (phi_pairs phi.inst_operands),
       case FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands) of
         NONE => matching | SOME (_,w) => matching |+ (i,w)))
      (om,mm) items)) idx = SOME src
Proof
  Induct >- simp[] >> rpt gen_tac >> Cases_on `h` >>
  rename1 `(i,phi) :: items` >> simp[NoAsms] >>
  disch_then (CONJUNCTS_THEN2 strip_assume_tac assume_tac) >>
  first_x_assum irule >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_x_assum `EVERY _ items` kall_tac >>
  Cases_on `i = idx`
  >- (qpat_x_assum `i = idx ==> _` drule >> strip_tac >>
      qpat_x_assum `MEM _ _ ==> _` kall_tac >>
      gvs[fnLineageStaticTheory.phi_pair_updates_lookup, FLOOKUP_UPDATE]) >>
  `~MEM v (MAP SND (phi_pairs phi.inst_operands))` by metis_tac[] >>
  qpat_x_assum `MEM _ _ ==> _` kall_tac >>
  qpat_x_assum `i = idx ==> _` kall_tac >>
  Cases_on `FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands)` >>
  gvs[fnLineageStaticTheory.phi_pair_updates_lookup, FLOOKUP_UPDATE, AllCaseEqs()] >>
  rename1 `FIND _ _ = SOME found` >> Cases_on `found` >>
  simp[FLOOKUP_UPDATE]
QED

Theorem fmp_phi_index_unique[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  j < LENGTH (collect_phis bb.bb_instructions) /\
  EL i (collect_phis bb.bb_instructions) =
    EL j (collect_phis bb.bb_instructions) ==> i = j
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\q. q.inst_id) bb.bb_instructions)` by
    (irule all_distinct_flat_mem >>
     qexists_tac `MAP (\b. MAP (\q. q.inst_id) b.bb_instructions) fn.fn_blocks` >>
     conj_tac >- gvs[wf_function_def, fn_inst_ids_distinct_def] >>
     simp[MEM_MAP] >> qexists_tac `bb` >> simp[]) >>
  `EL i (collect_phis bb.bb_instructions) = EL i bb.bb_instructions /\
   EL j (collect_phis bb.bb_instructions) = EL j bb.bb_instructions`
    by metis_tac[collect_phis_index] >>
  drule ALL_DISTINCT_EL_IMP >>
  disch_then (qspecl_then [`i`,`j`] mp_tac) >>
  simp[EL_MAP] >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions`
    by simp[current_collect_phis_length] >>
  gvs[]
QED

Theorem fmp_ready_source_index[local]:
  wf_function fn /\ MEM bb fn.fn_blocks /\
  fmp_phi_ready_block (liveness_analyze fn) bb /\
  idx < LENGTH (collect_phis bb.bb_instructions) /\
  MEM u (MAP SND (phi_pairs
    (EL idx (collect_phis bb.bb_instructions)).inst_operands)) ==>
  !i. i < LENGTH (collect_phis bb.bb_instructions) /\
    MEM u (MAP SND (phi_pairs
      (EL i (collect_phis bb.bb_instructions)).inst_operands)) ==> i = idx
Proof
  strip_tac >> rpt strip_tac >>
  irule fmp_phi_index_unique >> qexistsl_tac [`bb`,`fn`] >> simp[] >>
  `MEM u (inst_uses (EL idx (collect_phis bb.bb_instructions))) /\
   MEM u (inst_uses (EL i (collect_phis bb.bb_instructions)))`
    by metis_tac[inst_uses_def, phi_pairs_mem_operand_vars] >>
  gvs[fmp_phi_ready_block_def, EVERY_MEM] >>
  metis_tac[EL_MEM]
QED

Theorem fmp_ready_selected_input[local]:
  wf_function fn /\ fn_inst_wf fn /\ MEM bb fn.fn_blocks /\
  fmp_phi_ready_block (liveness_analyze fn) bb /\
  MEM phi (collect_phis bb.bb_instructions) /\
  resolve_phi pred phi.inst_operands = SOME (Var u) /\ MEM u live ==>
  MEM u (input_vars_from pred bb.bb_instructions live)
Proof
  strip_tac >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI`
    by metis_tac[collect_phis_mem] >>
  `inst_wf phi` by metis_tac[fn_inst_wf_def] >>
  `phi_well_formed phi.inst_operands` by gvs[inst_wf_def] >>
  drule fmp_resolve_find_pairs >>
  disch_then (qspec_then `pred` mp_tac) >>
  Cases_on `FIND (\(l,w). l = pred) (phi_pairs phi.inst_operands)` >>
  gvs[] >> rename1 `FIND _ _ = SOME found` >> Cases_on `found` >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `FIND _ _ = SOME (label,u)` >>
  `label = pred` by (drule venomInstTheory.FIND_P >> simp[]) >> gvs[] >>
  `MEM u (MAP SND (phi_pairs phi.inst_operands))`
    by (drule venomInstTheory.FIND_MEM >> simp[MEM_MAP] >> metis_tac[SND]) >>
  qpat_x_assum `MEM phi (collect_phis _)`
    (strip_assume_tac o REWRITE_RULE [MEM_EL]) >> rename1 `idx < LENGTH _` >>
  `!i. i < LENGTH (collect_phis bb.bb_instructions) /\
     MEM u (MAP SND (phi_pairs
       (EL i (collect_phis bb.bb_instructions)).inst_operands)) ==> i = idx`
    by metis_tac[fmp_ready_source_index] >>
  rename1 `resolve_phi pred _ = _` >>
  mp_tac (Q.SPECL [`MAPi (\i phi. (i,phi)) (collect_phis bb.bb_instructions)`,
    `FEMPTY`, `FEMPTY`, `pred`, `u`, `idx`, `u`] fmp_maps_fold_selected) >>
  impl_tac
  >- (conj_tac
      >- (simp[EVERY_MEM, MEM_MAPi, FORALL_PROD] >> rpt strip_tac >> gvs[])
      >> simp[MEM_MAP, MEM_MAPi] >> qexists_tac `(idx,phi)` >> simp[] >>
      qexists_tac `idx` >> simp[]) >>
  strip_tac >> irule input_vars_from_trigger_maps >>
  qexistsl_tac [`idx`,
    `SND (build_phi_maps pred (collect_phis bb.bb_instructions))`,
    `FST (build_phi_maps pred (collect_phis bb.bb_instructions))`, `u`] >>
  simp[build_phi_maps_def]
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

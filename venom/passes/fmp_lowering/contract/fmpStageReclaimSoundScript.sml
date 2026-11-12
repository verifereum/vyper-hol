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
  pair finite_map indexedLists livenessDefs venomFnInstsProofs fnLineageStatic
  fmpLowerReclaimPlan venomWfProps removeUnusedProofs
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
  strip_tac >> irule fresh_out_conditional >>
  qexistsl [`bb`, `fn`, `infos`, `k`, `states`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac
  >- metis_tac[reclaim_fresh_edge]
  >- metis_tac[reclaim_fresh_index_some]
  >> metis_tac[reclaim_fresh_entry]
QED

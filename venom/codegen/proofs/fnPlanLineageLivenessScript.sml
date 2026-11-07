Theory fnPlanLineageLiveness
Ancestors
  stackPlanGen livenessConvergenceProofs livenessAnalysisProps venomInst
  cfgNormSupplyProofs livenessProofs
Libs
  livenessDefsTheory livenessBlockProofsTheory

Theorem analyzed_live_out_singleton:
  !fn pred succ pred_bb succ_bb.
    wf_function fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block succ fn.fn_blocks = SOME succ_bb /\
    cfg_succs_of (cfg_analyze fn) pred = [succ] ==>
    set (live_vars_at (liveness_analyze fn) pred
      (LENGTH pred_bb.bb_instructions)) =
    set (input_vars_from pred succ_bb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0))
Proof
  rpt strip_tac >> drule_all liveness_recompute_convergence >>
  simp[same_vars_set, liveness_instrs_def, liveness_out_def,
       liveness_edge_transfer_def, liveness_analyze_def, live_vars_at_def,
       dfHelperDefsTheory.list_union_def]
QED

Theorem analyzed_live_out_edge_subset:
  !fn pred succ pred_bb succ_bb.
    wf_function fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block succ fn.fn_blocks = SOME succ_bb /\
    MEM succ (cfg_succs_of (cfg_analyze fn) pred) ==>
    set (input_vars_from pred succ_bb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0)) SUBSET
    set (live_vars_at (liveness_analyze fn) pred
      (LENGTH pred_bb.bb_instructions))
Proof
  rpt strip_tac >> drule_all liveness_recompute_edge_subset >>
  simp[liveness_instrs_def, liveness_edge_transfer_def,
       liveness_analyze_def, live_vars_at_def]
QED

Theorem analyzed_live_out_jmp:
  !fn pred succ pred_bb succ_bb inst.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block succ fn.fn_blocks = SOME succ_bb /\
    pred_bb.bb_instructions <> [] /\ LAST pred_bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label succ] ==>
    set (live_vars_at (liveness_analyze fn) pred
      (LENGTH pred_bb.bb_instructions)) =
    set (input_vars_from pred succ_bb.bb_instructions
      (live_vars_at (liveness_analyze fn) succ 0))
Proof
  rpt strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  irule analyzed_live_out_singleton >> simp[] >>
  `pred_bb.bb_label = pred` by
    (qpat_assum `lookup_block pred _ = _`
      (mp_tac o MATCH_MP venomExecPropsTheory.lookup_block_label) >> simp[]) >>
  qpat_x_assum `lookup_block pred _ = _` mp_tac >>
  simp[venomInstTheory.lookup_block_def] >>
  strip_tac >> drule FIND_SOME_MEM >> strip_tac >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs >>
  Cases_on `pred_bb.bb_instructions` >>
  gvs[venomInstTheory.bb_succs_def, venomInstTheory.get_successors_def,
      venomInstTheory.is_terminator_def, venomStateTheory.get_label_def,
      listTheory.nub_def]
QED

Theorem analyzed_dead_before_use_free_interval:
  !fn lbl bb i j v.
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  i <= j /\ j <= LENGTH bb.bb_instructions /\
  ~MEM v (live_vars_at (liveness_analyze fn) lbl j) /\
  (!k. i <= k /\ k < j ==> ~MEM v (inst_uses (EL k bb.bb_instructions))) ==>
  ~MEM v (live_vars_at (liveness_analyze fn) lbl i)
Proof
  Induct_on `j` >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `i = SUC j` >- gvs[] >>
  `i <= j` by decide_tac >>
  `~MEM v (live_vars_at (liveness_analyze fn) lbl j)` by
    (drule livenessAnalysisPropsTheory.live_vars_at_transfer >>
     disch_then (qspecl_then [`lbl`, `bb`, `j`] mp_tac) >>
     simp[] >>
     `~MEM v (inst_uses (EL j bb.bb_instructions))` by
       (first_x_assum irule >> decide_tac) >>
     simp[liveness_transfer_def, livenessProofsTheory.live_update_mem]) >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem collect_phis_prefix:
  !insts. ?rest. insts = collect_phis insts ++ rest
Proof
  Induct >- simp[livenessDefsTheory.collect_phis_def] >>
  simp[livenessDefsTheory.collect_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[] >> metis_tac[]
QED

Theorem phi_uses_disjoint_later:
  !phis i j v.
  phi_uses_disjoint phis /\ i < j /\ j < LENGTH phis /\
  MEM v (inst_uses (EL i phis)) ==> ~MEM v (inst_uses (EL j phis))
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[phi_uses_disjoint_def] >> strip_tac >>
  Cases_on `i` >- (Cases_on `j` >> gvs[listTheory.EVERY_MEM] >> metis_tac[listTheory.EL_MEM]) >>
  Cases_on `j` >> gvs[] >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem analyzed_phi_incoming_dead_after:
  !fn lbl bb i k v.
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
  phi_block_ready (liveness_analyze fn) bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  i < k /\ k <= LENGTH (collect_phis bb.bb_instructions) /\
  MEM v (inst_uses (EL i (collect_phis bb.bb_instructions))) ==>
  ~MEM v (live_vars_at (liveness_analyze fn) lbl k)
Proof
  rpt gen_tac >> strip_tac >>
  `?rest. bb.bb_instructions = collect_phis bb.bb_instructions ++ rest` by
    metis_tac[collect_phis_prefix] >>
  irule analyzed_dead_before_use_free_interval >> simp[] >>
  qexists_tac `LENGTH (collect_phis bb.bb_instructions)` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `EL k' bb.bb_instructions = EL k' (collect_phis bb.bb_instructions)` by
        metis_tac[rich_listTheory.EL_APPEND1] >>
      gvs[phi_block_ready_def] >>
      drule phi_uses_disjoint_later >>
      disch_then (qspecl_then [`i`, `k'`, `v`] mp_tac) >> simp[]) >>
  conj_tac
  >- (gvs[phi_block_ready_def, listTheory.EVERY_MEM] >>
      `i < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
      metis_tac[listTheory.EL_MEM]) >>
  qpat_assum `bb.bb_instructions = _` mp_tac >>
  disch_then (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[]
QED

Theorem analyzed_ready_phi_live_through_edge:
  !fn lbl bb pred v.
    wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
    phi_block_ready (liveness_analyze fn) bb /\
    MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions))) /\
    EVERY (\inst. ~MEM v (inst_defs inst)) (collect_phis bb.bb_instructions) ==>
    MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0))
Proof
  rpt strip_tac >>
  qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl 0)` by
    (drule livenessAnalysisPropsTheory.live_vars_at_propagate_range >>
     disch_then (qspecl_then [`lbl`, `bb`, `0`,
       `LENGTH (collect_phis bb.bb_instructions)`, `v`] mp_tac) >>
     simp[] >> impl_tac >-
       (qmatch_asmsub_abbrev_tac `bb.bb_instructions = phis ++ rest` >>
        qpat_x_assum `bb.bb_instructions = _` SUBST1_TAC >>
        gvs[listTheory.EVERY_EL, listTheory.EL_APPEND_EQN]) >> simp[]) >>
  irule livenessProofsTheory.input_vars_from_non_phi >> simp[] >>
  rpt strip_tac >>
  gvs[phi_block_ready_def, listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
  drule cfgNormSupplyProofsTheory.MEM_phi_pairs_SND_operand_vars_pair >>
  gvs[venomInstTheory.inst_uses_def] >> metis_tac[]
QED

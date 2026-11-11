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
  drule_all cfgCorrectnessProofTheory.cfg_analyze_preserves_bb_succs >>
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
    (drule livenessProofsTheory.live_vars_at_transfer >>
     disch_then (qspecl_then [`lbl`, `bb`, `j`] mp_tac) >>
     simp[] >>
     `~MEM v (inst_uses (EL j bb.bb_instructions))` by
       (first_x_assum irule >> decide_tac) >>
     simp[liveness_transfer_def, livenessTransferProofsTheory.live_update_mem]) >>
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

(* Endpoint-driven first definition. Deadness excludes explicit requests,
   but does not imply physical erasure or exclude implicit JMP targets. *)
Theorem analyzed_first_definition:
  !fn lbl bb a b v.
    wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    a <= b /\ b <= LENGTH bb.bb_instructions /\
    ~MEM v (live_vars_at (liveness_analyze fn) lbl a) /\
    MEM v (live_vars_at (liveness_analyze fn) lbl b) ==>
    ?k. a <= k /\ k < b /\
      MEM v (inst_defs (EL k bb.bb_instructions)) /\
      (!r. a <= r /\ r <= k ==>
        ~MEM v (live_vars_at (liveness_analyze fn) lbl r)) /\
      (!r. a <= r /\ r <= k ==>
        ~MEM (Var v) (EL r bb.bb_instructions).inst_operands) /\
      (!r. a <= r /\ r < k ==>
        ~MEM v (EL r bb.bb_instructions).inst_outputs)
Proof
  rpt gen_tac >> strip_tac >>
  `?k. a <= k /\ k < b /\ MEM v (inst_defs (EL k bb.bb_instructions))` by
    (spose_not_then assume_tac >>
     `MEM v (live_vars_at (liveness_analyze fn) lbl a)` suffices_by simp[] >>
     irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_propagate_range) >>
     simp[] >> qexists_tac `b` >> simp[] >>
     rpt strip_tac >> first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
  qexists_tac `LEAST k. a <= k /\ k < b /\ MEM v (inst_defs (EL k bb.bb_instructions))` >>
  numLib.LEAST_ELIM_TAC >> conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `!r. a <= r /\ r <= n ==>
      ~MEM v (live_vars_at (liveness_analyze fn) lbl r)` by
    (rpt strip_tac >>
     `MEM v (live_vars_at (liveness_analyze fn) lbl a)` suffices_by simp[] >>
     irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_propagate_range) >>
     simp[] >> qexists_tac `r` >> simp[] >>
     qx_gen_tac `t` >> strip_tac >>
     qpat_x_assum `!m. _` (qspec_then `t` mp_tac) >>
     `t < n /\ a <= t /\ t < b` by decide_tac >> simp[]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `MEM v (inst_uses (EL r bb.bb_instructions))` by
        simp[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
      drule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_uses) >>
      disch_then (qspecl_then [`lbl`, `bb`, `r`, `v`] mp_tac) >>
      `r < LENGTH bb.bb_instructions` by decide_tac >>
      simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!m. m < n ==> _` (qspec_then `r` mp_tac) >>
  gvs[inst_defs_def]
QED

(* Logical first reactivation only: this does not assert physical erasure
   or shielding of residual stack copies by the defining instruction. *)
Theorem analyzed_phi_incoming_first_reactivation:
  !fn lbl bb i j v.
    wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
    phi_block_ready (liveness_analyze fn) bb /\
    i < LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (inst_uses (EL i (collect_phis bb.bb_instructions))) /\
    i < j /\ j <= LENGTH bb.bb_instructions /\
    MEM v (live_vars_at (liveness_analyze fn) lbl j) ==>
    ?k. i < k /\ k < j /\ MEM v (inst_defs (EL k bb.bb_instructions)) /\
      (!r. i < r /\ r <= k ==>
        ~MEM v (live_vars_at (liveness_analyze fn) lbl r))
Proof
  rpt gen_tac >> strip_tac >>
  `~MEM v (live_vars_at (liveness_analyze fn) lbl (i+1))` by
    (irule analyzed_phi_incoming_dead_after >> simp[] >>
     qexists_tac `i` >> simp[]) >>
  drule analyzed_first_definition >>
  disch_then (qspecl_then [`lbl`, `bb`, `i+1`, `j`, `v`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `k` >> simp[]
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
    (drule livenessProofsTheory.live_vars_at_propagate_range >>
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

Theorem analyzed_entry_reachable:
  wf_function fn /\ fn_entry_label fn = SOME lbl ==>
  cfg_reachable_of (cfg_analyze fn) lbl
Proof
  strip_tac >> gvs[fn_entry_label_def, AllCaseEqs()] >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability >>
  simp[cfgDefsTheory.cfg_path_def, relationTheory.RTC_REFL]
QED

Theorem analyzed_successor_reachable:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  MEM succ (cfg_succs_of (cfg_analyze fn) pred) ==>
  cfg_reachable_of (cfg_analyze fn) succ
Proof
  strip_tac >>
  `?bb. entry_block fn = SOME bb` by
    (gvs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def,
         entry_block_def, listTheory.NULL_EQ] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability >>
  disch_then (fn th => fs[th, cfgDefsTheory.cfg_path_def]) >>
  irule relationTheory.RTC_TRANS >> qexists_tac `pred` >>
  simp[] >> irule relationTheory.RTC_SINGLE >> simp[]
QED

Theorem ready_phi_later_operand_isolated:
  !liveness bb i j v.
    phi_block_ready liveness bb /\ i < j /\
    j < LENGTH (collect_phis bb.bb_instructions) /\
    MEM (Var v) (EL j (collect_phis bb.bb_instructions)).inst_operands ==>
    ~MEM (Var v) (EL i (collect_phis bb.bb_instructions)).inst_operands
Proof
  simp[phi_block_ready_def, GSYM passSharedDefsTheory.MEM_operand_vars_eq_Var,
       GSYM venomInstTheory.inst_uses_def] >>
  metis_tac[phi_uses_disjoint_later]
QED

Theorem analyzed_phi_protected_demand:
  !fn bb k v.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
    k <= LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (collect_phis bb.bb_instructions))) /\
    EVERY (\inst. ~MEM v (inst_defs inst)) (DROP k (collect_phis bb.bb_instructions)) ==>
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label k)
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[venomWfPropsTheory.fn_reachable_in_cfg_dfs_pre] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    metis_tac[venomExecProofsTheory.wf_lookup_block] >>
  qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (qpat_assum `bb.bb_instructions = _`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[listTheory.LENGTH_APPEND]) >>
  irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_propagate_range) >>
  simp[] >> qexists_tac `LENGTH (collect_phis bb.bb_instructions)` >> simp[] >>
  rpt strip_tac >>
  `MEM (EL k' (collect_phis bb.bb_instructions))
       (DROP k (collect_phis bb.bb_instructions))` by
    (simp[listTheory.MEM_DROP] >> qexists_tac `k' - k` >> simp[]) >>
  `EL k' bb.bb_instructions = EL k' (collect_phis bb.bb_instructions)` by
    (qpat_x_assum `bb.bb_instructions = _` (fn th =>
       CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
     simp[listTheory.EL_APPEND_EQN]) >>
  gvs[listTheory.EVERY_MEM]
QED

Theorem phi_protected_demand_step:
  !phis k v. k < LENGTH phis ==>
    (EVERY (\inst. ~MEM v (inst_defs inst)) (DROP k phis) <=>
     ~MEM v (inst_defs (EL k phis)) /\
     EVERY (\inst. ~MEM v (inst_defs inst)) (DROP (SUC k) phis))
Proof
  rpt strip_tac >> drule rich_listTheory.DROP_CONS_EL >> simp[]
QED

(* Relocated from ReturnCut for shared ready-block phase layout consumers. *)
Theorem ordered_phis_ordinary_suffix:
  !insts.
    (!i j. i < j /\ j < LENGTH insts /\
      (EL j insts).inst_opcode = PHI ==> (EL i insts).inst_opcode = PHI) ==>
    EVERY (\inst. inst.inst_opcode <> PHI)
      (DROP (LENGTH (collect_phis insts)) insts)
Proof
  Induct >- simp[livenessDefsTheory.collect_phis_def] >>
  rpt strip_tac >> Cases_on `h.inst_opcode = PHI`
  >- (simp[livenessDefsTheory.collect_phis_def] >> first_x_assum irule >>
      rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  simp[livenessDefsTheory.collect_phis_def, listTheory.EVERY_EL] >>
  rpt strip_tac >> Cases_on `n` >> gvs[] >>
  first_x_assum (qspecl_then [`0`, `SUC n'`] mp_tac) >> simp[]
QED

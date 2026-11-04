Theory makeSsaCurrentDemand
Ancestors
  makeSsaCurrentDemandBoundary makeSsaCurrentAnalysis venomWf cfgDefs livenessDefs
  livenessBlockProofs livenessTerminationProofs
Libs
  listTheory arithmeticTheory venomInstTheory

(* Real demands end at ordinary reads or the operand selected on an edge.
   PHI reads at raw local slots are deliberately kept out of this relation. *)
Inductive current_demand:
[ordinary:]
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (EL i bb.bb_instructions).inst_opcode <> PHI /\
  MEM v (inst_uses (EL i bb.bb_instructions)) ==>
  current_demand fn v l i
[edge:]
  lookup_block l fn.fn_blocks = SOME bb /\
  MEM succ (bb_succs bb) /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM phi (collect_phis sb.bb_instructions) /\
  MEM (l,v) (phi_pairs phi.inst_operands) ==>
  current_demand fn v l (LENGTH bb.bb_instructions)
[skip:]
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  ~MEM v (inst_defs (EL i bb.bb_instructions)) /\
  current_demand fn v l (SUC i) ==>
  current_demand fn v l i
[cross:]
  lookup_block l fn.fn_blocks = SOME bb /\
  MEM succ (bb_succs bb) /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  current_demand fn v succ 0 ==>
  current_demand fn v l (LENGTH bb.bb_instructions)
End

Definition current_pending_def:
  current_pending fn v l i <=>
  ?bb k. lookup_block l fn.fn_blocks = SOME bb /\
    i <= k /\ k < LENGTH bb.bb_instructions /\
    (EL k bb.bb_instructions).inst_opcode = PHI /\
    MEM v (inst_uses (EL k bb.bb_instructions)) /\
    !j. i <= j /\ j < k ==> ~MEM v (inst_defs (EL j bb.bb_instructions))
End

Definition current_demand_state_def:
  current_demand_state fn st <=>
  !l bb i v. lookup_block l fn.fn_blocks = SOME bb /\
    i <= LENGTH bb.bb_instructions /\ MEM v (df_at [] st l i) ==>
    current_demand fn v l i \/ current_pending fn v l i
End

Theorem current_pending_no_phi_tail:
  lookup_block l fn.fn_blocks = SOME bb /\
  (!k. i <= k /\ k < LENGTH bb.bb_instructions ==>
       (EL k bb.bb_instructions).inst_opcode <> PHI) ==>
  ~current_pending fn v l i
Proof
  simp[current_pending_def] >> metis_tac[optionTheory.SOME_11]
QED

Theorem current_pending_exit:
  lookup_block l fn.fn_blocks = SOME bb ==>
  ~current_pending fn v l (LENGTH bb.bb_instructions)
Proof
  strip_tac >> irule current_pending_no_phi_tail >> simp[]
QED

Theorem current_demand_state_init:
  current_demand_state fn (init_df_state [] labels)
Proof
  simp[current_demand_state_def, dfAnalyzeDefsTheory.init_df_state_def,
       dfAnalyzeDefsTheory.df_at_def]
QED

Theorem current_pending_step:
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  ~MEM v (inst_defs (EL i bb.bb_instructions)) /\
  current_pending fn v l (SUC i) ==>
  current_pending fn v l i
Proof
  simp[current_pending_def] >> rpt strip_tac >>
  gvs[] >> qexists_tac `k` >> simp[] >> rpt strip_tac >>
  Cases_on `j = i` >> gvs[] >> first_x_assum irule >> simp[]
QED

Theorem current_demand_or_pending_step:
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  ~MEM v (inst_defs (EL i bb.bb_instructions)) /\
  (current_demand fn v l (SUC i) \/ current_pending fn v l (SUC i)) ==>
  current_demand fn v l i \/ current_pending fn v l i
Proof
  metis_tac[current_demand_rules, current_pending_step]
QED

Theorem current_demand_or_pending_use:
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  MEM v (inst_uses (EL i bb.bb_instructions)) ==>
  current_demand fn v l i \/ current_pending fn v l i
Proof
  strip_tac >> Cases_on `(EL i bb.bb_instructions).inst_opcode = PHI`
  >- (disj2_tac >> simp[current_pending_def] >> qexists_tac `i` >> simp[]) >>
  disj1_tac >> metis_tac[current_demand_rules]
QED

Theorem current_demand_or_pending_transfer:
  lookup_block l fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\
  (!v. MEM v live ==> current_demand fn v l (SUC i) \/ current_pending fn v l (SUC i)) ==>
  !v. MEM v (liveness_transfer fn.fn_blocks (EL i bb.bb_instructions) live) ==>
    current_demand fn v l i \/ current_pending fn v l i
Proof
  simp[liveness_transfer_def, livenessTransferProofsTheory.live_update_mem] >>
  metis_tac[current_demand_or_pending_use, current_demand_or_pending_step]
QED

Theorem backward_position_invariant[local]:
  !n P. P n /\ (!i. i < n /\ P (SUC i) ==> P i) ==>
    !i. i <= n ==> P i
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `P n` by (first_x_assum irule >> simp[]) >>
  `!i. i <= n ==> P i` by
    (qpat_x_assum `!P. P n /\ _ ==> _` (qspec_then `P` mp_tac) >>
     impl_tac >- (simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]) >> simp[]) >>
  qpat_x_assum `!P. P n /\ _ ==> _` kall_tac >> rpt strip_tac >>
  Cases_on `i = SUC n` >- metis_tac[] >>
  qpat_x_assum `!i. i <= n ==> _` irule >> decide_tac
QED

Theorem current_demand_block_slots:
  lookup_block l fn.fn_blocks = SOME bb /\
  (!v. MEM v (liveness_out fn.fn_blocks cfg l st) ==>
       current_demand fn v l (LENGTH bb.bb_instructions)) ==>
  !i. i <= LENGTH bb.bb_instructions ==>
    !v. MEM v (df_at [] (liveness_block fn.fn_blocks cfg l st) l i) ==>
      current_demand fn v l i \/ current_pending fn v l i
Proof
  strip_tac >> ho_match_mp_tac backward_position_invariant >> conj_tac
  >- (`bb.bb_instructions = liveness_instrs fn.fn_blocks l` by simp[liveness_instrs_def] >>
      asm_rewrite_tac[liveness_block_exit] >> metis_tac[]) >>
  rpt strip_tac >>
  `i < LENGTH (liveness_instrs fn.fn_blocks l)` by simp[liveness_instrs_def] >>
  drule liveness_block_transfer >> simp[liveness_instrs_def] >>
  disch_then (fn th => fs[th]) >>
  irule current_demand_or_pending_transfer >>
  qexistsl_tac [`bb`, `df_at [] (liveness_block fn.fn_blocks cfg l st) l (SUC i)`] >> simp[]
QED

Theorem current_wf_phi_operand_vars:
  !ops. phi_well_formed ops ==>
    operand_vars ops = MAP SND (phi_pairs ops)
Proof
  ho_match_mp_tac phi_pairs_ind >>
  simp[phi_well_formed_def, phi_pairs_def, operand_vars_def, operand_var_def]
QED

Theorem current_phi_in_prefix:
  !insts k. k < LENGTH insts /\
    (!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
       (EL i insts).inst_opcode = PHI) /\
    (EL k insts).inst_opcode = PHI ==>
    MEM (EL k insts) (collect_phis insts)
Proof
  Induct >- simp[] >> gen_tac >> Cases
  >- simp[collect_phis_def] >>
  simp[collect_phis_def] >> rpt strip_tac >>
  `h.inst_opcode = PHI` by
    (first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  simp[] >> disj2_tac >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]
QED

Theorem current_pending_phi_operand:
  wf_function fn /\ fn_inst_wf fn /\
  lookup_block l fn.fn_blocks = SOME bb /\ current_pending fn v l i ==>
  ?phi. MEM phi (collect_phis bb.bb_instructions) /\
        MEM v (MAP SND (phi_pairs phi.inst_operands))
Proof
  simp[current_pending_def] >> rpt strip_tac >> gvs[] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `MEM (EL k bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    (irule current_phi_in_prefix >> gvs[bb_well_formed_def] >> metis_tac[]) >>
  `inst_wf (EL k bb.bb_instructions)` by
    metis_tac[fn_inst_wf_def, MEM_EL] >>
  `phi_well_formed (EL k bb.bb_instructions).inst_operands` by
    gvs[inst_wf_def] >>
  qexists_tac `EL k bb.bb_instructions` >> simp[] >>
  drule current_wf_phi_operand_vars >>
  gvs[inst_uses_def] >> metis_tac[]
QED

Theorem current_demand_edge_transfer:
  wf_function fn /\ fn_inst_wf fn /\ current_demand_state fn st /\
  lookup_block l fn.fn_blocks = SOME bb /\ MEM succ (bb_succs bb) /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM v (liveness_edge_transfer fn.fn_blocks succ l (df_at [] st succ 0)) ==>
  current_demand fn v l (LENGTH bb.bb_instructions)
Proof
  strip_tac >> drule_all current_liveness_edge_origin >> strip_tac
  >- metis_tac[current_demand_rules] >>
  `current_demand fn v succ 0 \/ current_pending fn v succ 0` by
    (fs[current_demand_state_def] >> metis_tac[ZERO_LESS_EQ])
  >- metis_tac[current_demand_rules] >>
  drule_all current_pending_phi_operand >> metis_tac[]
QED

Theorem current_demand_cfg_successor:
  wf_function fn /\ lookup_block l fn.fn_blocks = SOME bb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) l) ==>
  MEM succ (bb_succs bb) /\ ?sb. lookup_block succ fn.fn_blocks = SOME sb
Proof
  strip_tac >>
  `fn_cfg_edge fn l succ` by metis_tac[current_cfg_edge_succs] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `MEM succ (bb_succs bb)` by
    (fs[fn_cfg_edge_def] >>
     drule_all venomExecPropsTheory.MEM_lookup_block >> gvs[]) >>
  simp[] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `MEM succ (fn_labels fn)` by metis_tac[wf_function_def, fn_succs_closed_def] >>
  gvs[fn_labels_def, MEM_MAP] >>
  metis_tac[venomExecPropsTheory.MEM_lookup_block]
QED

Theorem current_demand_out:
  wf_function fn /\ fn_inst_wf fn /\ current_demand_state fn st /\
  lookup_block l fn.fn_blocks = SOME bb /\
  MEM v (liveness_out fn.fn_blocks (cfg_analyze fn) l st) ==>
  current_demand fn v l (LENGTH bb.bb_instructions)
Proof
  simp[liveness_out_def, livenessTransferProofsTheory.mem_foldl_list_union, MEM_MAP] >>
  rpt strip_tac >>
  drule_all current_demand_cfg_successor >> strip_tac >>
  irule current_demand_edge_transfer >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem current_demand_state_block:
  wf_function fn /\ fn_inst_wf fn /\ current_demand_state fn st ==>
  current_demand_state fn (liveness_block fn.fn_blocks (cfg_analyze fn) h st)
Proof
  strip_tac >> simp[current_demand_state_def] >> rpt strip_tac >>
  Cases_on `l = h`
  >- (gvs[] >> irule current_demand_block_slots >>
      goal_assum (drule_at Any) >> simp[] >>
      metis_tac[current_demand_out]) >>
  fs[liveness_block_other_inst, current_demand_state_def] >> metis_tac[]
QED

Theorem current_demand_state_recompute:
  wf_function fn /\ fn_inst_wf fn ==>
  current_demand_state fn (liveness_recompute fn)
Proof
  strip_tac >> simp[liveness_recompute_def] >>
  irule (liveness_recompute_lift |> Q.INST
    [`Q` |-> `\p. current_demand_state fn (SND p)`] |> BETA_RULE) >>
  simp[current_demand_state_init] >> rpt strip_tac >>
  Cases_on `p` >> Cases_on `q` >> gvs[] >>
  Cases_on `liveness_changed fn.fn_blocks h r
    (liveness_block fn.fn_blocks (cfg_analyze fn) h r)` >>
  gvs[worklistDefsTheory.wl_step_def] >>
  metis_tac[current_demand_state_block]
QED

Theorem current_phi_index_before_prefix:
  !insts k. k < LENGTH insts /\
    (!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
       (EL i insts).inst_opcode = PHI) /\
    (EL k insts).inst_opcode = PHI ==>
    k < LENGTH (collect_phis insts)
Proof
  Induct >- simp[] >> gen_tac >> Cases
  >- simp[collect_phis_def] >>
  simp[collect_phis_def] >> rpt strip_tac >>
  `h.inst_opcode = PHI` by
    (first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  simp[] >> first_x_assum irule >> simp[] >>
  rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]
QED

Theorem current_pending_post_phi:
  wf_function fn /\ lookup_block l fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= i ==>
  ~current_pending fn v l i
Proof
  strip_tac >> irule current_pending_no_phi_tail >>
  qexists_tac `bb` >> simp[] >> rpt strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `k < LENGTH (collect_phis bb.bb_instructions)` by
    (irule current_phi_index_before_prefix >> gvs[bb_well_formed_def] >> metis_tac[]) >>
  decide_tac
QED

Theorem current_live_post_phi_demand:
  wf_function fn /\ fn_inst_wf fn /\
  lookup_block l fn.fn_blocks = SOME bb /\
  LENGTH (collect_phis bb.bb_instructions) <= i /\
  i <= LENGTH bb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) l i) ==>
  current_demand fn v l i
Proof
  strip_tac >>
  `current_demand_state fn (liveness_recompute fn)` by
    metis_tac[current_demand_state_recompute] >>
  `current_demand fn v l i \/ current_pending fn v l i` by
    (fs[current_demand_state_def, live_vars_at_def, liveness_analyze_def] >> metis_tac[]) >>
  metis_tac[current_pending_post_phi]
QED

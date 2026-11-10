Theory fnPlanLineagePhiInputExclusion
Ancestors
  fnPlanLineagePhiActivation fnPlanLineageLiveness
  removeUnusedSsaProofs phiBlock venomExecProofs cfgAnalysisProps
  stackPlanGen livenessDefs venomInst list rich_list

(* Exact statement copies from fnFrameStepsPhi, under the task's approved
   acyclic planner-leaf exception. Local helpers remain private here. *)
Theorem phi_codegen_block_ready:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks ==>
  phi_block_ready (liveness_analyze fn) bb
Proof
  simp[codegen_ready_fn_def, phi_operands_ready_def] >>
  Cases_on `EVERY (\b. NULL (collect_phis b.bb_instructions)) fn.fn_blocks` >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac
  >- (`collect_phis bb.bb_instructions = []` by
        (qpat_x_assum `EVERY _ fn.fn_blocks` mp_tac >>
         simp[listTheory.EVERY_MEM] >> metis_tac[listTheory.NULL_EQ]) >>
      simp[phi_block_ready_def, phi_uses_disjoint_def]) >>
  metis_tac[]
QED

Theorem phi_codegen_input_dead_after_prefix[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM v (inst_uses phi) ==>
  ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >> drule_all phi_codegen_block_ready >>
  simp[phi_block_ready_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem phi_codegen_edge_wf[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst (collect_phis bb.bb_instructions) ==>
  phi_edge_uses_wf fn bb inst
Proof
  strip_tac >> drule livenessProofsTheory.collect_phis_mem >> strip_tac >>
  gvs[codegen_ready_fn_def, venomWfTheory.def_dominates_uses_def] >>
  metis_tac[]
QED

Theorem phi_edge_operand_reachable[local]:
  !fn bb inst v.
    phi_edge_uses_wf fn bb inst /\ MEM (Var v) inst.inst_operands ==>
    fn_reachable fn bb.bb_label
Proof
  rpt gen_tac >> simp[venomWfTheory.phi_edge_uses_wf_def] >> strip_tac >>
  drule_all venomWfTheory.phi_well_formed_var_pair >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  gvs[venomWfTheory.def_available_at_def, venomWfTheory.fn_dominates_def] >>
  gvs[venomWfTheory.fn_reachable_def] >>
  metis_tac[relationTheory.RTC_RULES_RIGHT1]
QED

(* Exact copy from fnFrameStepsPhi.phi_pair_find_selected. *)
Theorem phi_pair_find_selected[local]:
  !pairs pred v.
    ALL_DISTINCT (MAP FST pairs) /\ MEM (pred,v) pairs ==>
    FIND (\(l,w). l = pred) pairs = SOME (pred,v)
Proof
  Induct >> simp[] >> rpt gen_tac >> PairCases_on `h` >>
  simp[listTheory.FIND_thm] >> strip_tac >> gvs[] >>
  Cases_on `h0 = pred` >> gvs[] >>
  metis_tac[listTheory.MEM_MAP, pairTheory.FST]
QED

(* Same statement as fnFrameStepsPhi.phi_selected_input_vars; use the
   existing planner activation interface instead of copying its map proof. *)
Theorem phi_selected_input_vars[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\
  MEM (p,v) (phi_pairs phi.inst_operands) ==>
  MEM v (input_vars_from p bb.bb_instructions
    (live_vars_at (liveness_analyze fn) bb.bb_label 0))
Proof
  strip_tac >>
  `phi_edge_uses_wf fn bb phi` by metis_tac[phi_codegen_edge_wf] >>
  `MEM (Var v) phi.inst_operands` by metis_tac[cfgNormBaseTheory.phi_pairs_mem_var] >>
  `fn_reachable fn bb.bb_label` by metis_tac[phi_edge_operand_reachable] >>
  `?entry. fn_entry_label fn = SOME entry /\ bb.bb_label <> entry` by
    (Cases_on `fn.fn_blocks` >> gvs[fn_entry_label_def, entry_block_def] >>
     gvs[codegen_ready_fn_def, venomWfTheory.wf_function_def, fn_labels_def,
         ALL_DISTINCT, MEM_MAP] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[codegen_ready_fn_def, venomWfTheory.wf_function_def, fn_labels_def]) >>
  `?i. i < LENGTH (collect_phis bb.bb_instructions) /\
    EL i (collect_phis bb.bb_instructions) = phi` by metis_tac[MEM_EL] >>
  `FIND (\(l,w). l = p) (phi_pairs phi.inst_operands) = SOME (p,v)` by
    (irule phi_pair_find_selected >>
     gvs[venomWfTheory.phi_edge_uses_wf_def]) >>
  irule reachable_phi_incoming_activated >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

(* Exact statement copy from fnFrameStepsPhi.phi_pair_live_out. *)
Theorem phi_pair_live_out[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\
  MEM (p,v) (phi_pairs phi.inst_operands) /\
  lookup_block p fn.fn_blocks = SOME pb ==>
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions))
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `phi_edge_uses_wf fn bb phi` by metis_tac[phi_codegen_edge_wf] >>
  `fn_reachable fn p /\ fn_cfg_edge fn p bb.bb_label` by
    (qpat_x_assum `phi_edge_uses_wf _ _ _`
       (strip_assume_tac o REWRITE_RULE [venomWfTheory.phi_edge_uses_wf_def]) >>
     first_x_assum drule >> strip_tac >>
     gvs[venomWfTheory.def_available_at_def, venomWfTheory.fn_dominates_def] >>
     metis_tac[]) >>
  `MEM p (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
  `cfg_reachable_of (cfg_analyze fn) p` by
    (drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >>
     simp[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[codegen_ready_fn_def, venomWfTheory.wf_function_def, fn_labels_def]) >>
  `MEM bb.bb_label (cfg_succs_of (cfg_analyze fn) p)` by
    (gvs[venomWfTheory.fn_cfg_edge_def] >>
     metis_tac[cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs]) >>
  drule_all livenessConvergenceProofsTheory.liveness_recompute_edge_subset >>
  simp[livenessBlockProofsTheory.liveness_instrs_def, liveness_edge_transfer_def,
       pred_setTheory.SUBSET_DEF] >> strip_tac >>
  simp[liveness_analyze_def, live_vars_at_def] >> first_x_assum irule >>
  drule_all phi_selected_input_vars >>
  simp[liveness_analyze_def, live_vars_at_def]
QED

(* Exact copies of fnFrameStepsPhi's backward-liveness dependency closure. *)
Theorem phi_unkilled_exit_live[local]:
  wf_function fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions)) /\
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions)) /\ i <= LENGTH bb.bb_instructions ==>
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)
Proof
  strip_tac >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
  irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_propagate_range) >>
  goal_assum drule >> simp[] >> qexists_tac `LENGTH bb.bb_instructions` >>
  simp[] >> rpt strip_tac >>
  `MEM (EL k bb.bb_instructions) bb.bb_instructions` by simp[listTheory.EL_MEM] >>
  qpat_x_assum `~MEM v (FLAT _)` mp_tac >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[venomInstTheory.inst_defs_def]
QED

Theorem phi_live_out_backward_edge[local]:
  codegen_ready_fn fn /\ fn_reachable fn p /\ fn_cfg_edge fn p q /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block q fn.fn_blocks = SOME qb /\
  ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) qb.bb_instructions)) /\
  MEM v (live_vars_at (liveness_analyze fn) q (LENGTH qb.bb_instructions)) ==>
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions))
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `qb.bb_label = q /\ pb.bb_label = p` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `MEM qb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `fn_reachable fn q` by
    (gvs[venomWfTheory.fn_reachable_def] >>
     metis_tac[relationTheory.RTC_RULES_RIGHT1]) >>
  `MEM p (cfg_analyze fn).cfg_dfs_pre /\ MEM q (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
  `MEM q (cfg_succs_of (cfg_analyze fn) p)` by
    (gvs[venomWfTheory.fn_cfg_edge_def] >>
     metis_tac[cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs]) >>
  `!i. i <= LENGTH qb.bb_instructions ==>
    MEM v (live_vars_at (liveness_analyze fn) q i)` by
    (rpt strip_tac >>
     qpat_assum `qb.bb_label = q` (rewrite_tac o single o SYM) >>
     irule phi_unkilled_exit_live >> simp[]) >>
  `LENGTH (collect_phis qb.bb_instructions) <= LENGTH qb.bb_instructions` by
    (Q.SPEC_TAC (`qb.bb_instructions`, `insts`) >> Induct >>
     simp[collect_phis_def] >> rw[]) >>
  irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_cross_block) >>
  goal_assum drule >> simp[] >> qexistsl_tac [`qb`, `q`] >> simp[] >>
  rpt strip_tac >>
  `MEM v (inst_uses inst)` by
    (gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var, listTheory.MEM_MAP,
         pairTheory.EXISTS_PROD] >> metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]) >>
  drule_all phi_codegen_input_dead_after_prefix >> metis_tac[]
QED

Theorem phi_live_out_backward_path[local]:
  !path fn v first_bb last_bb.
    codegen_ready_fn fn /\ is_fn_path fn path /\ path <> [] /\
    fn_reachable fn (HD path) /\
    lookup_block (HD path) fn.fn_blocks = SOME first_bb /\
    lookup_block (LAST path) fn.fn_blocks = SOME last_bb /\
    (!lbl. MEM lbl path ==> ?bb. lookup_block lbl fn.fn_blocks = SOME bb) /\
    (!lbl bb. MEM lbl (TL path) /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
      ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    MEM v (live_vars_at (liveness_analyze fn) (LAST path)
      (LENGTH last_bb.bb_instructions)) ==>
    MEM v (live_vars_at (liveness_analyze fn) (HD path)
      (LENGTH first_bb.bb_instructions))
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (head::tail)` >> Cases_on `tail`
  >- (strip_tac >> gvs[]) >>
  rename1 `is_fn_path fn (head::next::rest)` >>
  simp[venomWfTheory.is_fn_path_def] >> strip_tac >>
  `?next_bb. lookup_block next fn.fn_blocks = SOME next_bb` by metis_tac[] >>
  `fn_reachable fn next` by
    (gvs[venomWfTheory.fn_reachable_def] >>
     metis_tac[relationTheory.RTC_RULES_RIGHT1]) >>
  `MEM v (live_vars_at (liveness_analyze fn) next
      (LENGTH next_bb.bb_instructions))` by
    (qpat_x_assum `!fn v first_bb last_bb. _`
       (qspecl_then [`fn`, `v`, `next_bb`, `last_bb`] mp_tac) >>
     simp[] >> impl_tac >- (rpt conj_tac >> metis_tac[listTheory.MEM]) >>
     simp[]) >>
  irule phi_live_out_backward_edge >> goal_assum drule >>
  simp[] >> qexistsl_tac [`next`, `next_bb`] >> simp[] >> metis_tac[]
QED

Theorem phi_path_last_suffix[local]:
  !path fn target.
    is_fn_path fn path /\ MEM target path ==>
    ?tail. is_fn_path fn (target::tail) /\
      LAST (target::tail) = LAST path /\ ~MEM target tail /\
      (!lbl. MEM lbl (target::tail) ==> MEM lbl path)
Proof
  Induct >- simp[] >> rpt gen_tac >>
  rename1 `is_fn_path fn (head::rest)` >> strip_tac >>
  Cases_on `MEM target rest`
  >- (`is_fn_path fn rest` by
        (Cases_on `rest` >> gvs[venomWfTheory.is_fn_path_def]) >>
      first_x_assum drule_all >> strip_tac >>
      qexists_tac `tail` >> Cases_on `rest` >> gvs[] >> metis_tac[]) >>
  `head = target` by gvs[] >> gvs[] >>
  qexists_tac `rest` >> simp[]
QED

Theorem phi_defined_live_out_back[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs /\
  fn_dominates fn bb.bb_label p /\
  lookup_block p fn.fn_blocks = SOME pb /\
  MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions)) ==>
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions))
Proof
  strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `fn_reachable fn p` by gvs[venomWfTheory.fn_dominates_def] >>
  qpat_assum `fn_reachable fn p`
    (strip_assume_tac o REWRITE_RULE [venomWfTheory.fn_reachable_def]) >>
  drule venomExecProofsTheory.rtc_to_fn_path >> strip_tac >>
  `MEM bb.bb_label path` by
    (gvs[venomWfTheory.fn_dominates_def] >> metis_tac[]) >>
  `fn_reachable fn (HD path)` by
    (simp[venomWfTheory.fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL]) >>
  `!lbl. MEM lbl path ==> fn_reachable fn lbl` by
    metis_tac[removeUnusedSsaProofsTheory.is_fn_path_all_reachable] >>
  drule_all phi_path_last_suffix >> strip_tac >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  irule (SRULE [] (Q.SPEC `bb.bb_label::tail` phi_live_out_backward_path)) >>
  simp[] >> qexists_tac `pb` >> simp[] >>
  qexists_tac `tail` >> simp[] >>
  reverse conj_tac
  >- (rpt strip_tac >> metis_tac[removeUnusedSsaProofsTheory.fn_reachable_has_block, listTheory.MEM]) >>
  rpt gen_tac >> strip_tac >>
  rename1 `lookup_block lbl fn.fn_blocks = SOME other_bb` >>
  `MEM other_bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `other_bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  strip_tac >> gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  `other_bb = bb` by metis_tac[removeUnusedSsaProofsTheory.ssa_unique_output_block] >>
  metis_tac[]
QED

Theorem phi_prefix_outputs_disjoint_suffix[local]:
  !insts v.
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) insts)) /\
    MEM v (FLAT (MAP (\inst. inst.inst_outputs) (collect_phis insts))) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs)
      (DROP (LENGTH (collect_phis insts)) insts)))
Proof
  Induct >- simp[collect_phis_def] >> rpt gen_tac >>
  rename1 `collect_phis (head::tail)` >>
  Cases_on `head.inst_opcode = PHI` >>
  simp[collect_phis_def, listTheory.ALL_DISTINCT_APPEND] >>
  rpt strip_tac >> gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  `MEM inst tail` by
    (gvs[listTheory.MEM_DROP] >> metis_tac[listTheory.EL_MEM]) >>
  metis_tac[]
QED

Theorem phi_output_exit_live_prefix[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  MEM outphi (collect_phis bb.bb_instructions) /\ MEM v outphi.inst_outputs /\
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions)) ==>
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    metis_tac[phiBlockTheory.ssa_form_block_outputs_distinct] >>
  `~MEM v (FLAT (MAP (\inst. inst.inst_outputs)
    (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)))` by
    (irule phi_prefix_outputs_disjoint_suffix >> simp[] >>
     simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[removeUnusedSsaProofsTheory.fn_reachable_in_cfg_dfs_pre] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  `LENGTH (collect_phis bb.bb_instructions) <= LENGTH bb.bb_instructions` by
    (Q.SPEC_TAC (`bb.bb_instructions`, `insts`) >> Induct >>
     simp[collect_phis_def] >> rw[]) >>
  irule (SRULE [LET_THM] livenessProofsTheory.live_vars_at_propagate_range) >>
  goal_assum drule >> simp[] >> qexists_tac `LENGTH bb.bb_instructions` >>
  simp[] >> rpt strip_tac >>
  `MEM (EL k bb.bb_instructions)
    (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)` by
    (simp[listTheory.MEM_DROP] >>
     qexists_tac `k - LENGTH (collect_phis bb.bb_instructions)` >> simp[]) >>
  qpat_x_assum `~MEM v (FLAT _)` mp_tac >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[inst_defs_def]
QED

(* Exact statement and proof from fnFrameStepsPhi.phi_prefix_output_not_operand. *)
Theorem phi_prefix_output_not_operand:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ bb <> HD fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\
  MEM outphi (collect_phis bb.bb_instructions) /\ MEM v outphi.inst_outputs ==>
  ~MEM (Var v) phi.inst_operands
Proof
  strip_tac >> strip_tac >>
  `wf_function fn /\ ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `MEM outphi bb.bb_instructions` by
    metis_tac[livenessProofsTheory.collect_phis_mem] >>
  `phi_edge_uses_wf fn bb phi` by metis_tac[phi_codegen_edge_wf] >>
  `fn_reachable fn bb.bb_label` by metis_tac[phi_edge_operand_reachable] >>
  `?p. MEM (p,v) (phi_pairs phi.inst_operands)` by
    (gvs[venomWfTheory.phi_edge_uses_wf_def] >>
     metis_tac[venomWfTheory.phi_well_formed_var_pair]) >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = p /\
    def_available_at fn pb NONE v` by
    (gvs[venomWfTheory.phi_edge_uses_wf_def] >> metis_tac[]) >>
  `lookup_block p fn.fn_blocks = SOME pb` by
    (irule venomExecPropsTheory.MEM_lookup_block >>
     gvs[venomWfTheory.wf_function_def, fn_labels_def]) >>
  `fn_dominates fn bb.bb_label p` by
    (qpat_x_assum `def_available_at _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [venomWfTheory.def_available_at_def]) >>
     `def_bb = bb` by
       metis_tac[removeUnusedSsaProofsTheory.ssa_unique_output_block] >>
     gvs[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) p (LENGTH pb.bb_instructions))` by
    (irule phi_pair_live_out >> goal_assum drule >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions))` by
    (irule phi_defined_live_out_back >> goal_assum drule >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))` by
    (irule phi_output_exit_live_prefix >> goal_assum drule >> metis_tac[]) >>
  `MEM v (inst_uses phi)` by
    metis_tac[removeUnusedSsaProofsTheory.operand_var_in_inst_uses] >>
  metis_tac[phi_codegen_input_dead_after_prefix]
QED

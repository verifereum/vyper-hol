(*
 * Static facts about a lineage state (fnPlanLineage): the planner state a
 * run-time path reaches at a block's entry.  The block-entry prefix lemmas
 * (fnFrameSteps$phi_prefix_frame_sim, fnFrameSinglePred) and the block
 * body (fnBlockBody) need them of the state they start from.
 *
 * TOP-LEVEL:
 *   lineage_state_static - CHEATED: the state is well formed (repeated
 *                          dead_stack_marker slots allowed), and nothing on
 *                          its stack or in its spill map but the block's
 *                          PHI sources stands for a variable the block
 *                          defines (nothing at all with one predecessor);
 *                          it holds every live-in variable but the PHI
 *                          operands, and one source of each PHI
 *)

Theory fnLineageStatic
Ancestors
  fnPlanLineageJoin fnLineageInv fnLiveDefDom fnPlanPrefix fnPlanLineage
  stackPlanGen stackPlanTypes livenessDefs dfgDefs
  codegenReadyCompute venomExecProofs venomWf venomExecProps venomInst
  relation list finite_map dominatorProofs cfgAnalysisProps
  removeUnusedSsaProofs

Theorem lineage_state_entry_cases[local]:
  lineage_state liveness dfg cfg fn ps0 lbl ps ==>
  (fn_entry_label fn = SOME lbl /\ ps = ps0) \/
  (?pred. lineage_entry liveness dfg cfg fn ps0 pred lbl ps)
Proof
  simp[Once lineage_state_cases, lineage_entry_def] >> metis_tac[]
QED

Theorem lineage_state_reachable[local]:
  !liveness dfg cfg fn ps0 lbl ps.
    lineage_state liveness dfg cfg fn ps0 lbl ps ==>
    cfg = cfg_analyze fn /\ codegen_ready_fn fn ==>
    fn_reachable fn lbl
Proof
  rpt gen_tac >> qid_spec_tac `ps` >> qid_spec_tac `lbl` >>
  ho_match_mp_tac lineage_state_ind >> rpt strip_tac
  >- (simp[fn_reachable_def] >> metis_tac[relationTheory.RTC_REFL])
  >> irule fn_reachable_step >> qexists_tac `lbl` >>
  gvs[codegen_ready_fn_def] >>
  metis_tac[fn_cfg_edge_cfg_analyze]
QED

Theorem lineage_entry_edge[local]:
  lineage_entry liveness dfg (cfg_analyze fn) fn ps0 pred succ ps /\
  codegen_ready_fn fn ==>
  (?bb. lookup_block pred fn.fn_blocks = SOME bb) /\
  fn_cfg_edge fn pred succ /\ fn_reachable fn pred /\
  fn_reachable fn succ
Proof
  strip_tac >>
  `fn_reachable fn succ` by
    metis_tac[lineage_entry_lineage_state, lineage_state_reachable] >>
  gvs[lineage_entry_def] >>
  `fn_reachable fn pred` by metis_tac[lineage_state_reachable] >>
  gvs[codegen_ready_fn_def] >>
  metis_tac[fn_cfg_edge_cfg_analyze]
QED

Theorem ready_small_preds_no_phis[local]:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <= 1 ==>
  collect_phis bb.bb_instructions = []
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM] >>
  metis_tac[NULL_EQ]
QED

Theorem ready_entry_no_phis[local]:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  collect_phis bb.bb_instructions = []
Proof
  strip_tac >>
  `?eb. entry_block fn = SOME eb /\ eb.bb_label = lbl` by
    gvs[fn_entry_label_def, AllCaseEqs()] >>
  `MEM eb fn.fn_blocks` by
    (gvs[entry_block_def, AllCaseEqs()] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  `ALL_DISTINCT (fn_labels fn)` by
    gvs[codegen_ready_fn_def, wf_function_def] >>
  `lookup_block lbl fn.fn_blocks = SOME eb` by
    metis_tac[MEM_lookup_block, fn_labels_def] >>
  gvs[codegen_ready_fn_def, block_entries_ready_def, NULL_EQ]
QED

Theorem initial_cleanup_empty[local]:
  (init_cleanup_plan_state ch growth spill_base lbl_ctr).ps_stack = [] /\
  (init_cleanup_plan_state ch growth spill_base lbl_ctr).ps_spilled = FEMPTY
Proof
  simp[init_cleanup_plan_state_def, init_plan_state_def]
QED

Theorem dominates_entry_label[local]:
  fn_entry_label fn = SOME entry /\ fn_dominates fn dom entry ==>
  dom = entry
Proof
  rw[fn_dominates_def] >>
  first_x_assum (qspec_then `[entry]` mp_tac) >>
  simp[is_fn_path_def]
QED

Theorem ready_entry_no_preds[local]:
  codegen_ready_fn fn /\ entry_block fn = SOME eb ==>
  cfg_preds_of (cfg_analyze fn) eb.bb_label = []
Proof
  strip_tac >> gvs[codegen_ready_fn_def, block_entries_ready_def, NULL_EQ]
QED

Theorem small_preds_not_dominates_pred[local]:
  codegen_ready_fn fn /\ fn_reachable fn pred /\
  fn_cfg_edge fn pred succ /\
  LENGTH (cfg_preds_of (cfg_analyze fn) succ) <= 1 ==>
  ~fn_dominates fn succ pred
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `?eb. entry_block fn = SOME eb` by
    (gvs[wf_function_def, fn_has_entry_def, entry_block_def] >>
     Cases_on `fn.fn_blocks` >> gvs[]) >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) succ)` by
    metis_tac[fn_cfg_edge_cfg_analyze, cfg_edge_symmetry_uncond] >>
  `succ <> eb.bb_label` by metis_tac[ready_entry_no_preds, MEM] >>
  `cfg_reachable_of (cfg_analyze fn) succ` by
    metis_tac[fn_reachable_step, fn_reachable_cfg_analyze] >>
  drule_all exists_pred_not_dominated >>
  disch_then (qx_choose_then `other` strip_assume_tac) >>
  `other = pred` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) succ` >> gvs[] >>
     rename1 `SUC (LENGTH rest) <= 1` >> Cases_on `rest` >> gvs[]) >>
  metis_tac[fn_dominates_cfg_analyze]
QED

Theorem dominating_def_excludes_outputs[local]:
  codegen_ready_fn fn /\
  MEM def_bb fn.fn_blocks /\ MEM inst def_bb.bb_instructions /\
  MEM v inst.inst_outputs /\ fn_dominates fn def_bb.bb_label pred /\
  MEM target fn.fn_blocks /\ ~fn_dominates fn target.bb_label pred ==>
  ~MEM v (FLAT (MAP (\i. i.inst_outputs) target.bb_instructions))
Proof
  strip_tac >> strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[ssa_unique_output_block]
QED

Theorem strict_dominating_def_excludes_outputs[local]:
  codegen_ready_fn fn /\
  MEM def_bb fn.fn_blocks /\ MEM inst def_bb.bb_instructions /\
  MEM v inst.inst_outputs /\ fn_dominates fn def_bb.bb_label target.bb_label /\
  def_bb.bb_label <> target.bb_label /\ MEM target fn.fn_blocks ==>
  ~MEM v (FLAT (MAP (\i. i.inst_outputs) target.bb_instructions))
Proof
  strip_tac >> strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  gvs[MEM_FLAT, MEM_MAP] >>
  metis_tac[ssa_unique_output_block]
QED

(* Why it should hold.  Freshness: a join's entry stack is its JMP
   reorder's target, the predecessor-side PHI sources and the live-in
   variables; a source may be an output of the join itself (a loop header
   x = phi(a, v) whose body defines v), hence the exclusion of the PHI
   operands.  A live-in variable's definition strictly dominates the
   block, and so do the ASSIGN sources normalize_operand follows, so none
   is an output of the block.  A block with one predecessor P is entered
   with P's live-out variables (and markers), whose definitions dominate P
   and so the block, PHI sources included.  Well-formedness: a join is
   entered by a JMP, after which the spill map is empty (restore_spilled_plan,
   release_dead_spills), so only the successor's DFS allocator matters; a
   single-predecessor block is entered with the predecessor's spill map,
   which the lineage run allocates as the DFS run does (the stacks differ
   only in a bottom prefix of dead_stack_marker slots).  Coverage: the
   state holds every variable live at the end of the predecessor
   (fnLineageInv), and a live-in variable of the block that isn't a PHI
   operand is one of them; at the entry block nothing is live
   (fnLiveDefDom).  A PHI's operand from the entering edge is live at the
   end of that predecessor; its other operands are not (phi_uses_disjoint,
   phi_block_ready, and a join's predecessor has the join as its only
   successor).  A block with one predecessor has no PHIs
   (stackPlanGen$phis_at_joins). *)
Theorem lineage_state_static:
  !liveness dfg cfg ch growth spill_base lbl_ctr fn fn_ops ps_end lbl bb ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
      spill_base lbl_ctr = SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    lineage_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl ps
    ==>
    generated_plan_state_wf_marked spill_base ps /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
                              (collect_phis bb.bb_instructions))) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    (LENGTH (cfg_preds_of cfg lbl) <= 1 ==>
     !op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
            (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
            ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))) /\
    (!v. MEM v (live_vars_at liveness lbl 0) /\
         ~MEM (Var v) (FLAT (MAP (\inst. inst.inst_operands)
                              (collect_phis bb.bb_instructions))) ==>
         MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    EVERY (\phi. ?!v. MEM (Var v) phi.inst_operands /\
                      (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled))
      (collect_phis bb.bb_instructions)
Proof
  cheat
QED

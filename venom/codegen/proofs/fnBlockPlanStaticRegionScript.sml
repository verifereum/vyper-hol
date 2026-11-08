Theory fnBlockPlanStaticRegion
Ancestors
  fnBlockPlanStaticDfsTrace fnBlockPlanStaticPromises fnBlockPlanStaticInventory fnPlanLineage fnPlanLineageJoin
  planWfMarked fnLineageInv fnPlanPrefix list stackPlanGen fnFrameBoundaryGenRet codegenReadyCompute
  fnBlockPlanStaticOffsetLive livenessProofs livenessTransferProofs venomWf venomExecProofs rich_list
  removeUnusedSsaProofs venomInst cfgNormSupplyProofs cfgNormBase
  fnFrameBoundaryEntryParams stackModel genBlockSim fnLineageStatic fnBlockPlanStaticFacts
  dfgAnalysisProps dfgDefs allocaRemapSSA stackPlanOps planSpillBounds doSwapSim pair callLayoutDefs
  reorderSim stackPlanTypes fnFrameStepsRevertForward sorting planWf cleanOpsSim
  deepResidualSim deepResidualBudget genericInputReady fnAliasStep fnBlockPlanStaticRetRegion
  fnLineageInvSupport fnLineageInvOwnerOrigin fnLineageInvEdgeFacts
  livenessConvergenceProofs livenessBlockProofs livenessDefs
  fnFrameStepsPhi
  removeUnusedProofs fnPlanLineageLiveness venomWfProps
Theorem dfs_saved_parent_origin_mutual[local]:
  (!wl visited pg.
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg ==>
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg) /\
  (!ss sp succs visited pg.
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg /\
    ?lbl rest seen pin bb bops pout.
      dfs_aux_call lv dfg cfg fn ps0 (lbl::rest) seen pin /\
      ~MEM lbl seen /\ lookup_block lbl fn.fn_blocks = SOME bb /\
      generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
      ss = pout.ps_stack /\ sp = pout.ps_spilled /\
      (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl)))
Proof
  ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- metis_tac[dfs_aux_call_entry]
  >- metis_tac[dfs_aux_call_visited]
  >- metis_tac[dfs_aux_call_missing]
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[dfs_aux_call_succs]
      >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[])
  >- metis_tac[dfs_aux_call_rest]
  >- (rpt strip_tac >> irule dfs_aux_call_branch >>
      goal_assum (drule_at Any) >> simp[])
  >> rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[dfs_aux_call_sibling]
  >> metis_tac[listTheory.MEM]
QED

Theorem dfs_saved_parent_origin:
  dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
  ?lbl rest seen pin bb bops pout.
    dfs_aux_call lv dfg cfg fn ps0 (lbl::rest) seen pin /\
    ~MEM lbl seen /\ lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
    ss = pout.ps_stack /\ sp = pout.ps_spilled /\
    (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl))
Proof
  metis_tac[dfs_saved_parent_origin_mutual]
QED

Theorem dfs_saved_parent_block_origin:
  dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
  ?lbl pin bb bops pout.
    dfs_block_state lv dfg cfg fn ps0 lbl pin /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
    ss = pout.ps_stack /\ sp = pout.ps_spilled /\
    (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl))
Proof
  strip_tac >> drule dfs_saved_parent_origin >>
  simp[dfs_block_state_def] >> metis_tac[]
QED

Theorem regional_lineage_join_input_physical:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred bb ps v.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps /\
    MEM v (input_vars_from pred bb.bb_instructions
              (live_vars_at liveness bb.bb_label 0)) ==>
    MEM (Var v) ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >> drule_all lineage_entry_join_stack >>
  strip_tac >> gvs[listTheory.MEM_APPEND, listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem regional_lineage_join_target_distinct:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred pred_bb bb ps.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    lineage_entry liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred bb.bb_label ps ==>
    ALL_DISTINCT (MAP Var (input_vars_from pred bb.bb_instructions
                            (live_vars_at liveness bb.bb_label 0)))
Proof
  rpt strip_tac >>
  drule_all lineage_entry_inventory >> strip_tac >>
  drule_all lineage_entry_join_stack >> strip_tac >>
  gvs[generated_plan_state_wf_marked_def, FILTER_APPEND_DISTRIB,
      dead_stack_marker_def, EVERY_FILTER, ALL_DISTINCT_APPEND] >>
  `FILTER (\op. op <> Label "")
     (MAP Var (input_vars_from pred bb.bb_instructions
       (live_vars_at (liveness_analyze fn) bb.bb_label 0))) =
   MAP Var (input_vars_from pred bb.bb_instructions
       (live_vars_at (liveness_analyze fn) bb.bb_label 0))`
    by simp[FILTER_EQ_ID, EVERY_MAP] >>
  gvs[]
QED

Theorem dfs_lineage_branch[local]:
  lineage_state lv dfg cfg fn ps0 lbl pin /\
  dfs_block_state lv dfg cfg fn ps0 lbl pin /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
  MEM succ (cfg_succs_of cfg lbl) /\
  dfs_block_state lv dfg cfg fn ps0 succ
    (pg with <| ps_stack := pout.ps_stack; ps_spilled := pout.ps_spilled |>) ==>
  lineage_state lv dfg cfg fn ps0 succ
    (pg with <| ps_stack := pout.ps_stack; ps_spilled := pout.ps_spilled |> )
Proof
  strip_tac >>
  `pg with <| ps_stack := pout.ps_stack; ps_spilled := pout.ps_spilled |> =
   (pg with <| ps_stack := pout.ps_stack; ps_spilled := pout.ps_spilled |>)
     with <| ps_stack := pout.ps_stack; ps_spilled := pout.ps_spilled |>`
    by simp[] >>
  pop_assum SUBST1_TAC >> irule lineage_state_step >> simp[] >>
  goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`pin.ps_cleanup_height`, `pin.ps_cleanup_promised`] >>
  simp[]
QED

Theorem dfs_lineage_mutual[local]:
  (!wl visited pg.
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg ==>
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg /\
    !lbl rest. wl = lbl::rest ==>
      rest = [] /\ (~MEM lbl visited ==>
        lineage_state lv dfg cfg fn ps0 lbl pg)) /\
  (!ss sp succs visited pg.
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg /\
    ?lbl pin bb bops pout.
      lineage_state lv dfg cfg fn ps0 lbl pin /\
      dfs_block_state lv dfg cfg fn ps0 lbl pin /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      generate_block_plan lv dfg cfg fn bb pin = SOME (bops,pout) /\
      ss = pout.ps_stack /\ sp = pout.ps_spilled /\
      (!s. MEM s succs ==> MEM s (cfg_succs_of cfg lbl)))
Proof
  ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[dfs_aux_call_entry, lineage_state_entry])
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      metis_tac[dfs_aux_call_visited])
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      metis_tac[dfs_aux_call_missing])
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[dfs_aux_call_succs]
      >> goal_assum (drule_at (Pat `lookup_block _ _ = _`)) >>
      goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
      simp[dfs_block_state_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> gvs[] >>
      metis_tac[dfs_aux_call_rest])
  >- (rpt gen_tac >> strip_tac >> conj_asm1_tac
      >- metis_tac[dfs_aux_call_branch]
      >> rpt strip_tac >> gvs[] >>
      rename1 `~MEM next visited` >>
      `dfs_block_state lv dfg cfg fn ps0 next
         (pg with <| ps_stack := pout.ps_stack;
                     ps_spilled := pout.ps_spilled |>)`
        by (simp[dfs_block_state_def] >> metis_tac[]) >>
      `MEM next (cfg_succs_of cfg lbl)` by metis_tac[] >>
      drule_all dfs_lineage_branch >> simp[])
  >> rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[dfs_aux_call_sibling]
  >> metis_tac[MEM]
QED

Theorem dfs_aux_call_worklist_bound:
  dfs_aux_call lv dfg cfg fn ps0 wl visited pg ==> LENGTH wl <= 1
Proof
  strip_tac >> Cases_on `wl` >> simp[] >>
  drule (cj 1 dfs_lineage_mutual) >> simp[] >> metis_tac[]
QED

Theorem dfs_aux_call_inverse_origin_mutual[local]:
  (!wl visited pg.
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg ==>
    dfs_aux_call lv dfg cfg fn ps0 wl visited pg /\
    !succ rest. wl = succ::rest ==>
      (fn_entry_label fn = SOME succ /\ pg = ps0) \/
      (?pred pin bb ops pout.
        dfs_block_state lv dfg cfg fn ps0 pred pin /\
        lookup_block pred fn.fn_blocks = SOME bb /\
        generate_block_plan lv dfg cfg fn bb pin = SOME (ops,pout) /\
        MEM succ (cfg_succs_of cfg pred) /\
        pg.ps_stack = pout.ps_stack /\ pg.ps_spilled = pout.ps_spilled)) /\
  (!ss sp succs visited pg.
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg ==>
    dfs_succs_call lv dfg cfg fn ps0 ss sp succs visited pg)
Proof
  ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[dfs_aux_call_entry])
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[dfs_aux_call_visited]
      >> drule dfs_aux_call_worklist_bound >> rpt strip_tac >> gvs[])
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[dfs_aux_call_missing]
      >> drule dfs_aux_call_worklist_bound >> rpt strip_tac >> gvs[])
  >- metis_tac[dfs_aux_call_succs]
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[dfs_aux_call_rest]
      >> drule dfs_aux_call_worklist_bound >> rpt strip_tac >> gvs[])
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[dfs_aux_call_branch]
      >> rpt strip_tac >> gvs[] >>
      drule dfs_saved_parent_block_origin >> strip_tac >>
      disj2_tac >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[MEM])
  >> metis_tac[dfs_aux_call_sibling]
QED

Theorem dfs_block_state_inverse_origin:
  dfs_block_state lv dfg cfg fn ps0 succ ds ==>
    (fn_entry_label fn = SOME succ /\ ds = ps0) \/
    (?pred pin bb ops pout.
      dfs_block_state lv dfg cfg fn ps0 pred pin /\
      lookup_block pred fn.fn_blocks = SOME bb /\
      generate_block_plan lv dfg cfg fn bb pin = SOME (ops,pout) /\
      MEM succ (cfg_succs_of cfg pred) /\
      ds.ps_stack = pout.ps_stack /\ ds.ps_spilled = pout.ps_spilled)
Proof
  rewrite_tac[dfs_block_state_def] >> rpt strip_tac >>
  drule (cj 1 dfs_aux_call_inverse_origin_mutual) >>
  simp[dfs_block_state_def]
QED

Theorem regional_dfs_singleton_success:
  ~MEM lbl visited /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  generate_fn_plan_aux lv dfg cfg fn [lbl] visited ps =
    SOME (ops, seen, pend) ==>
  ?bops pout sops.
    generate_block_plan lv dfg cfg fn bb ps = SOME (bops,pout) /\
    generate_succs_plan lv dfg cfg fn pout.ps_stack pout.ps_spilled
      (cfg_succs_of cfg lbl) (lbl::visited) pout = SOME (sops,seen,pend) /\
    ops = bops ++ sops
Proof
  strip_tac >>
  qpat_x_assum `generate_fn_plan_aux _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_fn_plan_aux_def] >>
  simp[AllCaseEqs(), cj 1 generate_fn_plan_aux_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem regional_dfs_singleton_seen:
  generate_fn_plan_aux lv dfg cfg fn [lbl] visited ps =
    SOME (ops, seen, pend) ==> MEM lbl seen
Proof
  Cases_on `MEM lbl visited`
  >- (strip_tac >> drule generate_fn_plan_aux_visited_mono >>
      simp[pred_setTheory.SUBSET_DEF]) >>
  Cases_on `lookup_block lbl fn.fn_blocks`
  >- (simp[Once generate_fn_plan_aux_def, cj 1 generate_fn_plan_aux_def] >>
      rpt strip_tac >> gvs[]) >>
  strip_tac >> drule_all regional_dfs_singleton_success >> strip_tac >>
  drule generate_succs_plan_visited_mono >> simp[pred_setTheory.SUBSET_DEF]
QED

Theorem dfs_block_state_lineage_state:
  dfs_block_state lv dfg cfg fn ps0 lbl ps ==>
  lineage_state lv dfg cfg fn ps0 lbl ps
Proof
  simp[dfs_block_state_def] >> metis_tac[dfs_lineage_mutual]
QED

Theorem dfs_edge_lineage_entry:
  dfs_block_state lv dfg cfg fn ps0 pred pin /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  generate_block_plan lv dfg cfg fn pred_bb pin = SOME (ops,pout) /\
  MEM succ (cfg_succs_of cfg pred) /\
  dfs_block_state lv dfg cfg fn ps0 succ ps_succ /\
  pout.ps_spilled = ps_succ.ps_spilled ==>
  lineage_entry lv dfg cfg fn ps0 pred succ
    (ps_succ with <| ps_stack := pout.ps_stack;
                    ps_spilled := pout.ps_spilled |>)
Proof
  strip_tac >>
  `lineage_state lv dfg cfg fn ps0 pred pin`
    by metis_tac[dfs_block_state_lineage_state] >>
  simp[lineage_entry_def] >>
  goal_assum (drule_at (Pat `lineage_state _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`pin.ps_cleanup_height`, `pin.ps_cleanup_promised`] >>
  simp[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem regional_ret_operand_support_empty:
  inst.inst_opcode = RET /\ inst.inst_outputs = [] /\
  ALL_DISTINCT ps.ps_stack /\
  DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  LENGTH (compute_operands inst) <= 16 /\
  EVERY (\op. ?v. op = Var v /\ MEM op (compute_operands inst)) ps.ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan RET (compute_operands inst) [] ps)).ps_stack /\
  generate_inst_plan lv dfg cfg fn inst [] halting next_term lbl ps = SOME (ops,ps')
  ==> ps'.ps_stack = []
Proof
  strip_tac >>
  Cases_on `emit_input_plan RET (compute_operands inst) [] ps` >>
  rename1 `emit_input_plan _ _ _ _ = (iops,mid)` >>
  Cases_on `reorder_plan dfg (compute_operands inst) mid` >>
  rename1 `reorder_plan _ _ _ = (rops,arranged)` >>
  `EVERY (\op. ?v. op = Var v /\ (MEM v [] \/ MEM op (compute_operands inst)))
     ps.ps_stack` by simp[] >>
  `PERM (compute_operands inst) (compute_operands inst)` by simp[] >>
  `LENGTH (compute_operands inst) <= LENGTH mid.ps_stack` by gvs[] >>
  drule_all inventory_regular_core_live_support_unconditional >>
  simp[] >> strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def, is_pre_codegen_opcode_def,
       venomInstTheory.is_param_opcode_def, generate_regular_inst_plan_def,
       venomEffectsTheory.is_commutative_def, generate_emit_ops_def,
       asmIRTheory.venom_to_evm_name_def] >>
  strip_tac >> gvs[release_dead_spills_stack]
QED


(* At a join, every predecessor's DFS code leaves no spills: its JMP plan
   restores every target. *)
Theorem dfs_edge_spilled_join[local]:
  codegen_ready_fn fn /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn ps0 pred pin /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb pin =
    SOME (ops, pout) /\
  MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) ==>
  pout.ps_spilled = FEMPTY
Proof
  strip_tac >>
  `wf_function fn` by fs[codegen_ready_fn_def] >>
  `MEM succ (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_analyze_succ_labels,
              venomInstTheory.fn_labels_def] >>
  drule dfAnalyzeProofsTheory.lookup_block_exists >> strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) pred` by
    metis_tac[dfs_block_state_cfg_reachable] >>
  metis_tac[analyzed_join_edge_block_spills_empty]
QED

(* Along a CFG edge, the spill map pred's DFS code leaves is succ's DFS
   spill map.  At a join both are FEMPTY.  With a single predecessor,
   succ's owner is pred itself, whose DFS state is pin once the planner
   succeeded. *)
Theorem dfs_edge_spilled:
  !liveness dfg cfg fn ps0 pred pb pin ops pout succ ps_succ.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    dfs_block_state liveness dfg cfg fn ps0 pred pin /\
    lookup_block pred fn.fn_blocks = SOME pb /\
    generate_block_plan liveness dfg cfg fn pb pin = SOME (ops, pout) /\
    MEM succ (cfg_succs_of cfg pred) /\
    dfs_block_state liveness dfg cfg fn ps0 succ ps_succ /\
    (LENGTH (cfg_preds_of cfg succ) <> 1 \/
     ?ch growth sb ctr fn_ops pend.
       ps0 = init_cleanup_plan_state ch growth sb ctr /\
       generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
         sb ctr = SOME (fn_ops, pend)) ==>
    pout.ps_spilled = ps_succ.ps_spilled
Proof
  rpt gen_tac >>
  Cases_on `LENGTH (cfg_preds_of cfg succ) = 1`
  >- (strip_tac >> gvs[] >>
      `fn_entry_label fn <> SOME succ` by metis_tac[ready_incoming_nonentry] >>
      drule_all dfs_block_state_owner_origin >> strip_tac >>
      `MEM pred (cfg_preds_of (cfg_analyze fn) succ) /\
       MEM pred' (cfg_preds_of (cfg_analyze fn) succ)` by
        metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
      gvs[LENGTH_EQ_NUM_compute] >>
      `B = pin` by metis_tac[dfs_block_state_unique] >> gvs[]) >>
  strip_tac >> gvs[] >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ)` by
    (`MEM pred (cfg_preds_of (cfg_analyze fn) succ)` by
       metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
     Cases_on `cfg_preds_of (cfg_analyze fn) succ` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `fn_entry_label fn <> SOME succ` by metis_tac[ready_incoming_nonentry] >>
  drule_all dfs_block_state_owner_origin >> strip_tac >>
  `pout.ps_spilled = FEMPTY /\ A.ps_spilled = FEMPTY` by
    metis_tac[dfs_edge_spilled_join] >>
  gvs[]
QED

Theorem regional_dfs_join_target_distinct:
  !liveness dfg cfg fn ch growth spill_base lbl_ctr pred pred_bb bb pin
   ops pout ps_succ.
    liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) pred pin /\
    generate_block_plan liveness dfg cfg fn pred_bb pin = SOME (ops,pout) /\
    MEM bb.bb_label (cfg_succs_of cfg pred) /\
    dfs_block_state liveness dfg cfg fn
      (init_cleanup_plan_state ch growth spill_base lbl_ctr) bb.bb_label ps_succ ==>
    ALL_DISTINCT (MAP Var (input_vars_from pred bb.bb_instructions
                            (live_vars_at liveness bb.bb_label 0)))
Proof
  rpt gen_tac >> strip_tac >>
  `pout.ps_spilled = ps_succ.ps_spilled` by
    (irule dfs_edge_spilled >> simp[] >> metis_tac[]) >>
  drule_all dfs_edge_lineage_entry >>
  strip_tac >> drule_all regional_lineage_join_target_distinct >> simp[]
QED

Theorem ret_region_dfs_params_unpromised:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base ctr) lbl ps /\
  cfg_path cfg lbl target /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps else ([],ps)) =
    (param_ops,ps1) ==>
  ~ps1.ps_cleanup_promised
Proof
  strip_tac >> drule_all ret_region_dfs_block_unpromised >> strip_tac >>
  Cases_on `bb = HD fn.fn_blocks` >> gvs[] >>
  metis_tac[prepare_params_plan_promised, pairTheory.SND]
QED

Theorem ret_region_dfs_cleanup_physical:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base ctr) lbl ps /\
  cfg_path cfg lbl target /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps else ([],ps)) =
    (param_ops,ps1) ==>
  clean_stack_plan lv cfg fn bb ps1 =
    case cfg_preds_of cfg bb.bb_label of
      [pred] =>
        if LENGTH (cfg_succs_of cfg pred) <= 1 then ([],ps1)
        else (case lookup_block pred fn.fn_blocks of
          NONE => ([],ps1)
        | SOME pred_bb =>
          popmany_plan (MAP Var (FILTER (\v. ~MEM v
            (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)))
            (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)))) ps1)
    | _ => ([],ps1)
Proof
  strip_tac >>
  `~ps1.ps_cleanup_promised` by metis_tac[ret_region_dfs_params_unpromised] >>
  `!n. ~cleanup_elision_safe ps1.ps_cleanup_height ps1.ps_cleanup_growth cfg fn bb n` by
    metis_tac[inventory_ret_cleanup_not_safe] >>
  simp[clean_stack_plan_def, LET_THM]
QED

Theorem ret_region_dfs_cleanup_every:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  dfs_block_state lv dfg cfg fn
    (init_cleanup_plan_state ch growth spill_base ctr) lbl ps /\
  cfg_path cfg lbl target /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps else ([],ps)) =
    (param_ops,ps1) /\
  ALL_DISTINCT ps1.ps_stack /\ EVERY P ps1.ps_stack /\
  clean_stack_plan lv cfg fn bb ps1 = (ops,qs) ==>
  EVERY P qs.ps_stack
Proof
  strip_tac >> drule_all ret_region_dfs_cleanup_physical >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[] >>
  rename1 `_ = pred::rest` >> Cases_on `rest` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `lookup_block pred fn.fn_blocks` >> simp[] >>
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `popmany_plan items ps1` >>
  drule inventory_popmany >> disch_then (qspec_then `items` mp_tac) >>
  gvs[EVERY_MEM] >> metis_tac[pairTheory.SND]
QED

Theorem regional_no_use_dead_range:
  !n fn bb i v.
    wf_function fn /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    i + n <= LENGTH bb.bb_instructions /\
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (i + n)) /\
    (!j. i <= j /\ j < i + n ==>
      ~MEM v (inst_uses (EL j bb.bb_instructions))) ==>
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i))` by
    (first_x_assum irule >> fs[arithmeticTheory.ADD_CLAUSES] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule live_vars_at_transfer >> simp[] >>
  disch_then (qspecl_then [`bb.bb_label`, `bb`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  `~MEM v (inst_uses (EL i bb.bb_instructions))` by
    (first_x_assum irule >> decide_tac) >>
  simp[livenessDefsTheory.liveness_transfer_def, live_update_mem]
QED

Theorem regional_phi_later_uses[local] = fnPlanLineageLivenessTheory.phi_uses_disjoint_later

Theorem regional_ready_phi_source_dead:
  !fn bb i v.
    codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    i < LENGTH (collect_phis bb.bb_instructions) /\
    MEM v (inst_uses (EL i bb.bb_instructions)) ==>
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (i + 1))
Proof
  rpt gen_tac >> strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `phi_block_ready (liveness_analyze fn) bb` by
    (irule ready_phi_block >> simp[] >> metis_tac[lookup_block_mem]) >>
  `MEM v (inst_uses (EL i (collect_phis bb.bb_instructions)))` by
    metis_tac[collect_phis_index] >>
  `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (collect_phis bb.bb_instructions)))` by
    (gvs[phi_block_ready_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  irule regional_no_use_dead_range >> simp[] >>
  reverse conj_tac >- metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  qexists_tac `LENGTH (collect_phis bb.bb_instructions) - (i + 1)` >>
  `i + 1 <= LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  simp[] >> reverse conj_tac >- metis_tac[current_collect_phis_length] >>
  rpt strip_tac >>
  `j < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `i < j` by decide_tac >>
  gvs[phi_block_ready_def] >>
  metis_tac[regional_phi_later_uses, collect_phis_index]
QED

Theorem regional_ready_phi_physical_transfer:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  inst = EL i bb.bb_instructions /\ MEM src (inst_uses inst) /\
  nl = live_vars_at (liveness_analyze fn) bb.bb_label (i + 1) /\
  generate_phi_plan inst nl F ps = (ops, qs) /\
  inst.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand inst.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ALL_DISTINCT ps.ps_stack /\ ~MEM (Var out) ps.ps_stack /\
  Var out NOTIN FDOM ps.ps_spilled /\
  DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  EVERY (\op. op = Var src \/ ?v. op = Var v /\ MEM v live_support) ps.ps_stack /\
  (MEM out nl ==> MEM out live_support) ==>
  EVERY (\op. ?v. op = Var v /\ MEM v live_support) qs.ps_stack /\
  ALL_DISTINCT qs.ps_stack /\
  DISJOINT (set qs.ps_stack) (FDOM qs.ps_spilled) /\
  qs.ps_spilled = ps.ps_spilled /\
  (!x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var src) \/ (x = Var out /\ MEM out nl))
Proof
  strip_tac >>
  `~MEM src nl` by metis_tac[regional_ready_phi_source_dead] >>
  drule_all inventory_phi_mem >> strip_tac >>
  drule_all inventory_phi_distinct >> strip_tac >>
  drule_all inventory_phi_disjoint >> strip_tac >>
  drule_all inventory_phi_spilled >> strip_tac >>
  simp[] >> gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem regional_param_heads_distinct[local]:
  codegen_ready_fn fn ==>
  ALL_DISTINCT (MAP (\i. Var (HD i.inst_outputs))
    (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  strip_tac >> drule ready_entry_param_outputs_distinct >>
  `MAP (\i. Var (HD i.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions) =
    MAP Var (MAP (\i. HD i.inst_outputs)
      (get_params (HD fn.fn_blocks).bb_instructions))` by
    simp[MAP_MAP_o, combinTheory.o_DEF] >>
  simp[] >> strip_tac >> irule ALL_DISTINCT_MAP_INJ >> simp[]
QED

Theorem regional_params_dead_filter[local]:
  ALL_DISTINCT installed.ps_stack /\
  installed.ps_stack = MAP (\i. Var (HD i.inst_outputs)) params /\
  popmany_plan (FILTER is_var_operand
    (FILTER (\v. ~MEM (operand_to_string v) nl) installed.ps_stack)) installed = (ops,qs) ==>
  ALL_DISTINCT qs.ps_stack /\
  EVERY (\op. ?v. op = Var v /\ MEM v nl /\ MEM op installed.ps_stack) qs.ps_stack
Proof
  strip_tac >> conj_tac >- metis_tac[inventory_popmany_distinct] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule_all inventory_popmany_mem >>
  disch_then (qspec_then `op` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[MEM_FILTER, MEM_MAP] >>
  gvs[stackPlanTypesTheory.operand_to_string_def, stackPlanTypesTheory.is_var_operand_def]
QED

Theorem regional_prepare_params_inventory:
  codegen_ready_fn fn /\ lv = liveness_analyze fn /\
  prepare_params_plan lv fn (init_cleanup_plan_state ch growth sb ctr) = (ops,qs) ==>
  ALL_DISTINCT qs.ps_stack /\ qs.ps_spilled = FEMPTY /\
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at lv (HD fn.fn_blocks).bb_label
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) /\
    MEM op (MAP (\i. Var (HD i.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions))) qs.ps_stack
Proof
  strip_tac >>
  qpat_x_assum `prepare_params_plan _ _ _ = _` mp_tac >>
  simp[prepare_params_plan_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `get_params entry.bb_instructions` >>
  Cases_on `get_params entry.bb_instructions = []`
  >- (strip_tac >> gvs[init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def]) >>
  simp[parameter_stack_fold] >>
  qmatch_goalsub_abbrev_tac `popmany_plan items installed` >>
  pairarg_tac >> simp[] >>
  rename1 `popmany_plan items installed = (pops,mid)` >>
  `ALL_DISTINCT installed.ps_stack` by
    (simp[Abbr `installed`, init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def] >>
     metis_tac[regional_param_heads_distinct]) >>
  `installed.ps_spilled = FEMPTY` by
    simp[Abbr `installed`, init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def] >>
  `ALL_DISTINCT mid.ps_stack /\
   EVERY (\op. ?v. op = Var v /\
     MEM v (live_vars_at (liveness_analyze fn) entry.bb_label
       (LENGTH (get_params entry.bb_instructions))) /\
     MEM op installed.ps_stack) mid.ps_stack` by
    (irule regional_params_dead_filter >>
     goal_assum (drule_at Any) >>
     simp[Abbr `items`, Abbr `installed`] >>
     qexists_tac `get_params entry.bb_instructions` >> simp[]) >>
  `mid.ps_spilled = FEMPTY` by
    (qspecl_then [`items`, `installed`] mp_tac
       fnFrameStepsRevertForwardTheory.rf_popmany_spilled >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule inventory_optimistic_swap_resources >> simp[] >> strip_tac >>
  drule inventory_optimistic_swap_every >>
  strip_tac >>
  gvs[Abbr `installed`, init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def] >>
  metis_tac[fnFrameStepsRevertForwardTheory.rf_optimistic_spilled, pairTheory.SND]
QED

Theorem regional_prepare_params_support:
  codegen_ready_fn fn /\ lv = liveness_analyze fn /\
  prepare_params_plan lv fn (init_cleanup_plan_state ch growth sb ctr) = (ops,qs) ==>
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at lv (HD fn.fn_blocks).bb_label
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) /\
    MEM op (MAP (\i. Var (HD i.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions))) qs.ps_stack
Proof
  strip_tac >> drule_all regional_prepare_params_inventory >> simp[]
QED

Theorem regional_prepare_params_distinct:
  codegen_ready_fn fn /\ lv = liveness_analyze fn /\
  prepare_params_plan lv fn (init_cleanup_plan_state ch growth sb ctr) = (ops,qs) ==>
  ALL_DISTINCT qs.ps_stack
Proof
  strip_tac >> drule_all regional_prepare_params_inventory >> simp[]
QED

Theorem regional_prepare_params_spilled:
  codegen_ready_fn fn /\ lv = liveness_analyze fn /\
  prepare_params_plan lv fn (init_cleanup_plan_state ch growth sb ctr) = (ops,qs) ==>
  qs.ps_spilled = FEMPTY
Proof
  strip_tac >> drule_all regional_prepare_params_inventory >> simp[]
QED

Theorem regional_stack_find_exists[local]:
  !stk P. (?op. MEM op stk /\ P op) ==> ?d. stack_find P stk = SOME d
Proof
  Induct >> simp[stack_find_def] >> rpt gen_tac >>
  Cases_on `P h` >> simp[] >> strip_tac >>
  `?d. stack_find P stk = SOME d` by metis_tac[] >> simp[]
QED

Theorem regional_phi_physical_depth:
  MEM (Var src) phi.inst_operands /\ MEM (Var src) stk /\
  (!v. MEM (Var v) phi.inst_operands /\ MEM (Var v) stk ==> v = src) ==>
  ?d. stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) stk = SOME d /\
      d < LENGTH stk /\ stack_peek d stk = Var src
Proof
  strip_tac >>
  `?d. stack_find (\op. MEM op (FILTER is_var_operand phi.inst_operands))
       (REVERSE stk) = SOME d` by
    (irule regional_stack_find_exists >> qexists_tac `Var src` >>
     simp[MEM_FILTER, stackPlanTypesTheory.is_var_operand_def]) >>
  qexists_tac `d` >> simp[stack_get_phi_depth_def] >>
  drule planWfTheory.stack_find_bound >> simp[] >> strip_tac >>
  drule genBlockSimTheory.stack_find_el >> simp[MEM_FILTER] >> strip_tac >>
  `stack_peek d stk = EL d (REVERSE stk)` by
    (simp[stack_peek_def, EL_REVERSE] >>
     `PRE (LENGTH stk - d) = LENGTH stk - 1 - d` by decide_tac >> simp[]) >>
  `MEM (EL d (REVERSE stk)) stk` by
    metis_tac[MEM_EL, MEM_REVERSE, LENGTH_REVERSE] >>
  Cases_on `EL d (REVERSE stk)` >> gvs[stackPlanTypesTheory.is_var_operand_def]
QED


Theorem regional_first_entry_edge:
  !fn target. fn_reachable fn target /\ fn_entry_label fn <> SOME target ==>
    ?pred. fn_reachable fn pred /\ fn_cfg_edge fn pred target /\
      ~fn_dominates fn target pred
Proof
  rpt strip_tac >>
  `?entry. fn_entry_label fn = SOME entry /\
     RTC (fn_cfg_edge fn) entry target` by gvs[fn_reachable_def] >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM target path` by metis_tac[MEM_LAST_NOT_NIL] >>
  drule_all phi_path_first_prefix >> strip_tac >>
  `pre <> []` by (strip_tac >> gvs[]) >>
  `HD pre = entry` by (Cases_on `pre` >> gvs[]) >>
  drule_all phi_path_snoc_edge >> strip_tac >>
  qexists_tac `LAST pre` >> simp[] >> conj_tac
  >- (simp[fn_reachable_def] >>
      qspecl_then [`fn`, `pre`] mp_tac is_fn_path_rtc >> simp[]) >>
  strip_tac >> qpat_x_assum `fn_dominates _ _ _` mp_tac >>
  simp[fn_dominates_def] >>
  disj2_tac >> qexists_tac `pre` >> simp[]
QED

Theorem regional_phi_edge_source_fresh:
  !fn bb phi pred w.
    codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
    MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI /\
    MEM (pred,w) (phi_pairs phi.inst_operands) /\
    ~fn_dominates fn bb.bb_label pred ==>
    !inst. MEM inst bb.bb_instructions ==> ~MEM w inst.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  `ssa_form fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `phi_edge_uses_wf fn bb phi` by
    (gvs[def_dominates_uses_def] >> metis_tac[]) >>
  `?pred_bb. MEM pred_bb fn.fn_blocks /\ pred_bb.bb_label = pred /\
     def_available_at fn pred_bb NONE w` by
    (gvs[phi_edge_uses_wf_def] >> metis_tac[]) >>
  qpat_x_assum `def_available_at _ _ _ _` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  rpt strip_tac >>
  `def_bb = bb` by metis_tac[ssa_unique_output_block] >> gvs[]
QED

Theorem regional_phi_nonentry[local]:
  !fn bb phi. codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM phi (collect_phis bb.bb_instructions) ==>
    fn_entry_label fn <> SOME bb.bb_label
Proof
  rpt strip_tac >>
  `block_entries_ready (cfg_analyze fn) fn` by gvs[codegen_ready_fn_def] >>
  qpat_x_assum `codegen_ready_fn _` kall_tac >>
  Cases_on `fn.fn_blocks` >>
  gvs[fn_entry_label_def, entry_block_def, lookup_block_def,
      FIND_thm, block_entries_ready_def, NULL_EQ]
QED

Theorem regional_phi_live_trigger:
  !fn bb phi. codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM phi (collect_phis bb.bb_instructions) ==>
    ?w. MEM w (MAP SND (phi_pairs phi.inst_operands)) /\
        MEM w (live_vars_at (liveness_analyze fn) bb.bb_label 0)
Proof
  rpt gen_tac >> strip_tac >>
  `fn_entry_label fn <> SOME bb.bb_label` by metis_tac[regional_phi_nonentry] >>
  drule_all regional_first_entry_edge >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `phi_edge_uses_wf fn bb phi` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  `?w. MEM (pred,w) (phi_pairs phi.inst_operands)` by
    (gvs[phi_edge_uses_wf_def] >> Cases_on `p` >> gvs[] >> metis_tac[]) >>
  `!inst. MEM inst bb.bb_instructions ==> ~MEM w inst.inst_outputs` by
    metis_tac[regional_phi_edge_source_fresh] >>
  `?idx. idx < LENGTH bb.bb_instructions /\ EL idx bb.bb_instructions = phi` by
    metis_tac[MEM_EL] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  `MEM w (inst_uses phi)` by
    metis_tac[MEM_phi_pairs_SND_operand_vars, inst_uses_def] >>
  `MEM w (live_vars_at (liveness_analyze fn) bb.bb_label idx)` by
    (drule live_vars_at_uses >> simp[] >> disch_then irule >> metis_tac[]) >>
  qexists_tac `w` >> conj_tac >- (simp[MEM_MAP] >> metis_tac[pairTheory.SND]) >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >>
  simp[] >> qexists_tac `idx` >>
  simp[inst_defs_def] >> rpt strip_tac >>
  `k < LENGTH bb.bb_instructions` by decide_tac >>
  metis_tac[EL_MEM]
QED

Theorem regional_nonentry_lineage_edge[local]:
  !lv dfg cfg fn ps0 lbl ps.
    lineage_state lv dfg cfg fn ps0 lbl ps /\
    fn_entry_label fn <> SOME lbl ==>
    ?pred. lineage_entry lv dfg cfg fn ps0 pred lbl ps /\
           MEM lbl (cfg_succs_of cfg pred)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
  once_rewrite_tac[lineage_state_cases] >>
  simp[lineage_entry_def] >> metis_tac[]
QED

Theorem regional_lineage_phi_source:
  !fn lv dfg cfg bb ch growth sb ctr ps phi.
    codegen_ready_fn fn /\ lv = liveness_analyze fn /\
    dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn
      (init_cleanup_plan_state ch growth sb ctr) bb.bb_label ps /\
    MEM phi (collect_phis bb.bb_instructions) ==>
    ?src. MEM (Var src) phi.inst_operands /\ MEM (Var src) ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn_entry_label fn <> SOME bb.bb_label` by metis_tac[regional_phi_nonentry] >>
  drule_all regional_nonentry_lineage_edge >> strip_tac >>
  `fn_reachable fn bb.bb_label` by
    (drule lineage_state_dfs_fields >> strip_tac >>
     drule_all dfs_block_state_cfg_reachable >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `phi_edge_uses_wf fn bb phi` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  `fn_cfg_edge fn pred bb.bb_label` by metis_tac[fn_cfg_edge_cfg_analyze] >>
  `?src. MEM (pred,src) (phi_pairs phi.inst_operands)` by
    (gvs[phi_edge_uses_wf_def] >> Cases_on `p` >> gvs[] >> metis_tac[]) >>
  drule_all regional_phi_live_trigger >> strip_tac >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    (drule_all ready_phi_block >> simp[phi_block_ready_def]) >>
  `MEM src (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by
    (irule input_vars_from_trigger_phi >> simp[] >> qexistsl_tac [`phi`, `w`] >>
     gvs[phi_edge_uses_wf_def]) >>
  `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1` by
    (strip_tac >>
     `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <= 1` by simp[] >>
     gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM, NULL_EQ] >>
     metis_tac[MEM]) >>
  qexists_tac `src` >> conj_tac >- metis_tac[phi_pairs_mem_var] >>
  irule regional_lineage_join_input_physical >> simp[] >>
  goal_assum (drule_at (Pat `lineage_entry _ _ _ _ _ _ _ _`)) >> simp[]
QED

Theorem regional_lineage_phi_depth:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps phi.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps /\ MEM phi (collect_phis bb.bb_instructions) ==>
    ?src d. MEM (Var src) phi.inst_operands /\ MEM (Var src) ps.ps_stack /\
      stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
      d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
      (!v. MEM (Var v) phi.inst_operands /\
        (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all regional_lineage_phi_source >> strip_tac >>
  drule_all lineage_state_static >> strip_tac >>
  `?!v. MEM (Var v) phi.inst_operands /\
      (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled)` by
    (qpat_x_assum `EVERY _ (collect_phis _)` mp_tac >>
     simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
  `!v. MEM (Var v) phi.inst_operands /\
      (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src` by
    metis_tac[EXISTS_UNIQUE_THM] >>
  `?d. stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
       d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src` by
    (irule regional_phi_physical_depth >> simp[]) >>
  qexistsl_tac [`src`, `d`] >> simp[] >> metis_tac[]
QED

(* Frame a future PHI independently of the representation used for the overwrite. *)
Theorem regional_phi_stack_frame:
  (!x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var removed) \/ (x = Var added /\ keep)) /\
  ~MEM (Var removed) phi.inst_operands /\
  ~MEM (Var added) phi.inst_operands ==>
  !v. MEM (Var v) phi.inst_operands ==>
    (MEM (Var v) qs.ps_stack <=> MEM (Var v) ps.ps_stack)
Proof
  rpt strip_tac >> first_x_assum (qspec_then `Var v` mp_tac) >>
  metis_tac[]
QED

Theorem regional_phi_owned_frame:
  qs.ps_spilled = ps.ps_spilled /\
  (!x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var removed) \/ (x = Var added /\ keep)) /\
  ~MEM (Var removed) phi.inst_operands /\
  ~MEM (Var added) phi.inst_operands ==>
  !v. MEM (Var v) phi.inst_operands ==>
    ((MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) <=>
     (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled))
Proof
  rpt strip_tac >>
  qpat_x_assum `!x. MEM x _ <=> _` (qspec_then `Var v` mp_tac) >>
  metis_tac[]
QED

Theorem regional_phi_selected_frame:
  qs.ps_spilled = ps.ps_spilled /\
  (!x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var removed) \/ (x = Var added /\ keep)) /\
  ~MEM (Var removed) phi.inst_operands /\
  ~MEM (Var added) phi.inst_operands /\
  MEM (Var src) phi.inst_operands /\ MEM (Var src) ps.ps_stack /\
  (!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src) ==>
  MEM (Var src) qs.ps_stack /\
  (!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled) ==> v = src)
Proof
  strip_tac >>
  drule_all regional_phi_stack_frame >> strip_tac >>
  drule_all regional_phi_owned_frame >> strip_tac >>
  metis_tac[]
QED

(* A PHI output has no further definition after the complete PHI prefix.
   This is independent of whether that output occurs on an incoming edge. *)
Theorem regional_phi_output_no_suffix_def:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs ==>
  !p. LENGTH (collect_phis bb.bb_instructions) <= p /\
      p < LENGTH bb.bb_instructions ==>
      ~MEM v (inst_defs (EL p bb.bb_instructions))
Proof
  strip_tac >>
  `?k. k < LENGTH (collect_phis bb.bb_instructions) /\
       EL k (collect_phis bb.bb_instructions) = phi` by metis_tac[MEM_EL] >>
  `EL k bb.bb_instructions = phi` by metis_tac[collect_phis_index] >>
  qx_gen_tac `p` >> strip_tac >> simp[inst_defs_def] >>
  irule ready_output_other_location >> simp[] >>
  qexistsl_tac [`bb`, `fn`, `k`] >> simp[] >>
  mp_tac (Q.SPEC `bb.bb_instructions` current_collect_phis_length) >> decide_tac
QED

Theorem regional_phi_output_exit_live:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs /\
  fn_reachable fn bb.bb_label /\
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH bb.bb_instructions)) ==>
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[] >> gvs[wf_function_def, fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >> simp[] >>
  qexists_tac `LENGTH bb.bb_instructions` >> simp[current_collect_phis_length] >>
  metis_tac[regional_phi_output_no_suffix_def]
QED

Theorem regional_live_range[local]:
  codegen_ready_fn fn /\ fn_reachable fn lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  i <= j /\ j <= LENGTH bb.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) lbl j) /\
  (!p. i <= p /\ p < j ==> ~MEM v (inst_defs (EL p bb.bb_instructions))) ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl i)
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  drule live_vars_at_propagate_range >> simp[] >> disch_then irule >> simp[] >>
  metis_tac[]
QED

Theorem regional_live_edge[local]:
  codegen_ready_fn fn /\ fn_reachable fn pred /\ fn_reachable fn lbl /\
  fn_cfg_edge fn pred lbl /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) /\
  (!p. p < LENGTH (collect_phis bb.bb_instructions) ==>
    ~MEM v (inst_defs (EL p bb.bb_instructions))) ==>
  MEM v (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions))
Proof
  strip_tac >> irule input_vars_from_predecessor_exit >> simp[] >>
  (conj_tac >- gvs[codegen_ready_fn_def]) >>
  qexistsl_tac [`bb`, `lbl`] >> simp[] >>
  irule ready_postprefix_edge >> simp[] >>
  conj_tac >- metis_tac[lookup_block_label] >>
  irule fn_reachable_in_cfg_dfs_pre >> gvs[codegen_ready_fn_def]
QED

Theorem regional_phi_other_block_no_defs[local]:
  codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
  MEM phi (collect_phis db.bb_instructions) /\ MEM v phi.inst_outputs /\
  lbl <> db.bb_label /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  p < LENGTH bb.bb_instructions ==> ~MEM v (inst_defs (EL p bb.bb_instructions))
Proof
  strip_tac >> simp[inst_defs_def] >>
  `?k. k < LENGTH (collect_phis db.bb_instructions) /\
       EL k (collect_phis db.bb_instructions) = phi` by metis_tac[MEM_EL] >>
  `EL k db.bb_instructions = phi` by metis_tac[collect_phis_index] >>
  irule ready_output_other_location >> simp[] >>
  qexistsl_tac [`db`, `fn`, `k`] >> simp[] >>
  `k < LENGTH db.bb_instructions` by
    (mp_tac (Q.SPEC `db.bb_instructions` current_collect_phis_length) >> decide_tac) >>
  metis_tac[lookup_block_MEM, lookup_block_label]
QED

Theorem regional_phi_output_dominated_boundary_live:
  codegen_ready_fn fn /\ MEM db fn.fn_blocks /\
  MEM phi (collect_phis db.bb_instructions) /\ MEM v phi.inst_outputs /\
  MEM ub fn.fn_blocks /\ fn_dominates fn db.bb_label ub.bb_label /\
  LENGTH (collect_phis ub.bb_instructions) <= j /\
  j <= LENGTH ub.bb_instructions /\
  MEM v (live_vars_at (liveness_analyze fn) ub.bb_label j) ==>
  MEM v (live_vars_at (liveness_analyze fn) db.bb_label
    (LENGTH (collect_phis db.bb_instructions)))
Proof
  strip_tac >>
  `fn_reachable fn db.bb_label` by metis_tac[fn_dominates_dom_reachable] >>
  `lookup_block db.bb_label fn.fn_blocks = SOME db /\
   lookup_block ub.bb_label fn.fn_blocks = SOME ub` by
    (conj_tac >> irule MEM_lookup_block >> simp[] >>
     gvs[codegen_ready_fn_def, wf_function_def, fn_labels_def]) >>
  Cases_on `ub = db`
  >- (gvs[] >> irule regional_live_range >> simp[] >>
      qexists_tac `j` >> simp[] >>
      qx_gen_tac `p` >> strip_tac >>
      irule regional_phi_output_no_suffix_def >> simp[] >>
      metis_tac[]) >>
  drule fn_dominates_last_visit >> strip_tac >>
  Cases_on `tail` >- (gvs[] >> metis_tac[]) >>
  rename1 `is_fn_path fn (db.bb_label :: first :: rest)` >>
  `?fb. lookup_block first fn.fn_blocks = SOME fb` by
    (`wf_function fn` by gvs[codegen_ready_fn_def] >>
     `cfg_reachable_of (cfg_analyze fn) first` by
       (gvs[] >> metis_tac[fn_reachable_cfg_analyze]) >>
     drule cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels >>
     simp[fn_labels_def, MEM_MAP] >> strip_tac >>
     irule_at Any MEM_lookup_block >> simp[] >>
     gvs[wf_function_def, fn_labels_def] >> metis_tac[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) first
      (LENGTH (collect_phis fb.bb_instructions)))` by
    (irule (SRULE [] (Q.SPEC `first :: rest` ready_live_path)) >> simp[] >>
     (conj_tac >- gvs[]) >> qexistsl_tac [`j`, `rest`, `ub`] >>
     gvs[Once is_fn_path_def] >> rpt gen_tac >> strip_tac >>
     irule regional_phi_other_block_no_defs >> simp[] >>
     qexistsl_tac [`db`, `fn`, `lbl`, `phi`] >> simp[] >> metis_tac[]) >>
  irule regional_phi_output_exit_live >> simp[] >>
  (conj_tac >- (qexists_tac `phi` >> simp[])) >>
  irule regional_live_edge >> simp[] >>
  qexistsl_tac [`fb`, `first`] >> gvs[Once is_fn_path_def] >>
  qx_gen_tac `p` >> disch_tac >>
  irule regional_phi_other_block_no_defs >> simp[] >>
  (conj_tac >- (mp_tac (Q.SPEC `fb.bb_instructions` current_collect_phis_length) >> decide_tac)) >>
  qexistsl_tac [`db`, `fn`, `first`, `phi`] >> simp[]
QED

Theorem regional_phi_selected_edge_exit_live:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\
  MEM phi (collect_phis bb.bb_instructions) /\
  MEM (pred,v) (phi_pairs phi.inst_operands) /\
  lookup_block pred fn.fn_blocks = SOME pb /\ fn_reachable fn pred ==>
  MEM v (live_vars_at (liveness_analyze fn) pred
    (LENGTH pb.bb_instructions))
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[] >>
     gvs[wf_function_def, fn_labels_def]) >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `phi_edge_uses_wf fn bb phi` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  `fn_cfg_edge fn pred bb.bb_label /\
   ALL_DISTINCT (MAP FST (phi_pairs phi.inst_operands))` by
    (gvs[phi_edge_uses_wf_def] >> metis_tac[]) >>
  drule_all regional_phi_live_trigger >> strip_tac >>
  `phi_block_ready (liveness_analyze fn) bb` by metis_tac[ready_phi_block] >>
  `MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by
    (irule input_vars_from_trigger_phi >>
     (conj_tac >- gvs[phi_block_ready_def]) >>
     qexistsl_tac [`phi`, `w`] >> simp[]) >>
  irule input_vars_from_predecessor_exit >> simp[] >>
  qexistsl_tac [`bb`, `bb.bb_label`] >> simp[]
QED

Theorem regional_phi_output_not_phi_source:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  fn_reachable fn bb.bb_label /\
  MEM defphi (collect_phis bb.bb_instructions) /\
  MEM v defphi.inst_outputs /\
  MEM usephi (collect_phis bb.bb_instructions) ==>
  ~MEM v (inst_uses usephi)
Proof
  strip_tac >> disch_tac >>
  `MEM usephi bb.bb_instructions /\ usephi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `phi_edge_uses_wf fn bb usephi` by
    (gvs[codegen_ready_fn_def, def_dominates_uses_def] >> metis_tac[]) >>
  `?pred. MEM (pred,v) (phi_pairs usephi.inst_operands)` by
    (irule phi_well_formed_var_pair >>
     gvs[phi_edge_uses_wf_def, inst_uses_def,
         passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `?pb. MEM pb fn.fn_blocks /\ pb.bb_label = pred /\
    fn_cfg_edge fn pred bb.bb_label /\ def_available_at fn pb NONE v` by
    metis_tac[phi_edge_uses_wf_def] >>
  `?k. k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = defphi` by
    metis_tac[collect_phis_mem, MEM_EL] >>
  `fn_dominates fn bb.bb_label pb.bb_label` by
    (irule (cj 1 ready_output_available) >> simp[] >>
     qexistsl_tac [`k`, `NONE`, `v`] >> simp[]) >>
  `fn_reachable fn pred` by metis_tac[fn_dominates_def] >>
  `lookup_block pred fn.fn_blocks = SOME pb` by
    (irule MEM_lookup_block >> simp[] >>
     gvs[codegen_ready_fn_def, wf_function_def, fn_labels_def]) >>
  `MEM v (live_vars_at (liveness_analyze fn) pred
    (LENGTH pb.bb_instructions))` by
    (irule regional_phi_selected_edge_exit_live >> simp[] >>
     qexistsl_tac [`bb`, `usephi`] >> simp[]) >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
    (LENGTH (collect_phis bb.bb_instructions)))` by
    (irule regional_phi_output_dominated_boundary_live >> simp[] >>
     (conj_tac >- (qexists_tac `defphi` >> simp[])) >>
     qexistsl_tac [`LENGTH pb.bb_instructions`, `pb`] >>
     simp[current_collect_phis_length]) >>
  `phi_block_ready (liveness_analyze fn) bb` by metis_tac[ready_phi_block] >>
  gvs[phi_block_ready_def, EVERY_MEM] >> metis_tac[]
QED

Theorem regional_phi_output_normalize:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  MEM phi (collect_phis bb.bb_instructions) /\ MEM v phi.inst_outputs ==>
  normalize_operand (dfg_build_function fn) [] (Var v) = Var v
Proof
  strip_tac >>
  `MEM phi bb.bb_instructions /\ phi.inst_opcode = PHI` by
    metis_tac[collect_phis_mem] >>
  `MEM phi (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[]) >>
  drule_all dfg_build_function_defs_complete >> strip_tac >>
  rename1 `dfg_get_def (dfg_build_function fn) v = SOME found` >>
  `found = phi` by
    (drule dfg_build_function_correct >> strip_tac >>
     `ssa_form fn` by gvs[codegen_ready_fn_def] >>
     metis_tac[ssa_unique_output]) >>
  gvs[dfg_get_def_def] >> simp[Once normalize_operand_def]
QED

Theorem regional_output_root_origin:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\ MEM out inst.inst_outputs ==>
  normalize_operand (dfg_build_function fn) [] (Var out) = Var out \/
  ?op. MEM op (compute_operands inst) /\
    normalize_operand (dfg_build_function fn) [] (Var out) =
      normalize_operand (dfg_build_function fn) [] op
Proof
  strip_tac >>
  `ssa_form fn /\ inst_wf inst` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM,
         fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >> metis_tac[]) >>
  `dfg_get_def (dfg_build_function fn) out = SOME inst` by
    metis_tac[dfg_build_function_ssa_def] >>
  Cases_on `inst.inst_opcode = ASSIGN`
  >- (`LENGTH inst.inst_operands = 1` by gvs[inst_wf_def] >>
      `?op. inst.inst_operands = [op]` by
        (qpat_x_assum `LENGTH _ = 1` mp_tac >> simp[LENGTH_EQ_NUM_compute]) >>
      disj2_tac >> qexists_tac `op` >>
      conj_tac >- simp[compute_operands_def] >>
      irule normalize_operand_codegen_assign >> simp[] >>
      qexists_tac `inst` >> simp[]) >>
  disj1_tac >> gvs[dfg_get_def_def] >> simp[Once normalize_operand_def]
QED

Theorem regional_indexed_outputs_separate[local]:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\
  i < j /\ j < LENGTH bb.bb_instructions /\
  MEM v (EL i bb.bb_instructions).inst_outputs ==>
  ~MEM v (EL j bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `ssa_form fn` by gvs[codegen_ready_fn_def] >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `i = j` by metis_tac[removeUnusedProofsTheory.ssa_form_no_dup_in_block] >>
  gvs[]
QED

Theorem regional_nonvar_root[local]:
  ~is_var_operand op ==>
  op <> Var v /\ normalize_operand dfg [] op <> Var v
Proof
  Cases_on `op` >> simp[is_var_operand_def, normalize_operand_def]
QED

Theorem regional_new_output_fresh[local]:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  (!v. MEM v inst.inst_outputs ==> ~MEM v later.inst_outputs) /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (op = Var v \/ normalize_operand (dfg_build_function fn) [] op = Var v) ==>
    ~MEM v later.inst_outputs) /\ MEM out inst.inst_outputs ==>
  !v. (Var out = Var v \/
    normalize_operand (dfg_build_function fn) [] (Var out) = Var v) ==>
    ~MEM v later.inst_outputs
Proof
  strip_tac >>
  drule_all regional_output_root_origin >> strip_tac
  >- (gvs[] >> metis_tac[]) >>
  Cases_on `is_var_operand op`
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[regional_nonvar_root]
QED

Theorem regional_indexed_body_suffix_freshness:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  generate_inst_plan lv (dfg_build_function fn) cfg fn inst nl halting next_term
    bb.bb_label ps = SOME (ops,qs) /\
  (!j op v. i <= j /\ j < LENGTH bb.bb_instructions /\
    (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (op = Var v \/ normalize_operand (dfg_build_function fn) [] op = Var v) ==>
    ~MEM v (EL j bb.bb_instructions).inst_outputs) ==>
  !j op v. SUC i <= j /\ j < LENGTH bb.bb_instructions /\
    (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) /\
    (op = Var v \/ normalize_operand (dfg_build_function fn) [] op = Var v) ==>
    ~MEM v (EL j bb.bb_instructions).inst_outputs
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `inst_wf inst` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def, EVERY_MEM] >> metis_tac[EL_MEM]) >>
  `inst.inst_opcode = OFFSET ==> ?out. inst.inst_outputs = [out]` by
    metis_tac[inst_wf_offset_shape] >>
  drule generate_inst_plan_inventory >> simp[] >>
  disch_then assume_tac >>
  rpt gen_tac >> disch_tac >>
  `i < j /\ i <= j` by gvs[] >>
  `!out. MEM out inst.inst_outputs ==> ~MEM out (EL j bb.bb_instructions).inst_outputs` by
    (gen_tac >> disch_tac >> irule regional_indexed_outputs_separate >>
     simp[] >> conj_tac >- (qexists_tac `fn` >> simp[]) >>
     qexists_tac `i` >> gvs[]) >>
  `!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (op = Var v \/ normalize_operand (dfg_build_function fn) [] op = Var v) ==>
    ~MEM v (EL j bb.bb_instructions).inst_outputs` by metis_tac[] >>
  `!out v. MEM out inst.inst_outputs /\
    (Var out = Var v \/ normalize_operand (dfg_build_function fn) [] (Var out) = Var v) ==>
    ~MEM v (EL j bb.bb_instructions).inst_outputs` by
    (rpt gen_tac >> strip_tac >> irule regional_new_output_fresh >>
     goal_assum (drule_at (Pat `MEM _ _.inst_outputs`)) >> simp[] >>
     qexistsl_tac [`fn`, `ps`] >> gvs[] >> metis_tac[]) >>
  metis_tac[regional_nonvar_root]
QED

Theorem regional_fresh_exemption_transfer:
  (!op:operand. op IN old /\ ~(op IN C UNION R) ==>
    fresh op /\ fresh (root op)) /\
  (!op. op IN old /\ op IN C ==> op = removed) /\
  (!op. op IN new ==> (op IN old /\ op <> removed) \/ op = added) /\
  fresh added /\ root added = added ==>
  (!op. op IN new /\ ~(op IN R) ==> fresh op /\ fresh (root op))
Proof
  simp[pred_setTheory.IN_UNION] >> metis_tac[]
QED

Theorem regional_phi_owned_subtraction:
  generate_phi_plan phi nl halting ps = (ops,qs) /\ phi.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ generated_plan_state_wf_marked sb ps /\
  ~MEM (Var out) ps.ps_stack ==>
  !op. (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) <=>
    ((MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\ op <> Var src) \/
    (op = Var out /\ (halting \/ MEM out nl))
Proof
  strip_tac >>
  `ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack) /\
   DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled)` by
    gvs[generated_plan_state_wf_marked_def] >>
  `MEM (Var src) ps.ps_stack` by
    (qpat_x_assum `stack_peek _ _ = _` (mp_tac o SYM) >>
     simp[stack_peek_def] >> strip_tac >> irule EL_MEM >> decide_tac) >>
  `Var src NOTIN FDOM ps.ps_spilled` by
    (gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  drule_all inventory_marked_phi_mem >> strip_tac >>
  drule_all inventory_marked_phi_spilled >> strip_tac >>
  gvs[] >> metis_tac[]
QED

Theorem regional_phi_freshness_step:
  generate_phi_plan phi nl halting ps = (ops,qs) /\ phi.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ generated_plan_state_wf_marked sb ps /\
  ~MEM (Var out) ps.ps_stack /\
  (!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src) /\
  (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    ~MEM op (phi.inst_operands ++ remaining_ops) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v future_outputs) /\
  ~MEM out future_outputs /\ normalize_operand dfg [] (Var out) = Var out ==>
  !op v. (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) /\
    ~MEM op remaining_ops /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v future_outputs
Proof
  strip_tac >> drule_all regional_phi_owned_subtraction >> disch_tac >>
  rpt gen_tac >> strip_tac >>
  (Cases_on `op = Var out` >- gvs[] >>
  `(MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\ op <> Var src` by
    metis_tac[] >>
  (Cases_on `MEM op phi.inst_operands`
   >- (Cases_on `op` >> gvs[] >> metis_tac[normalize_operand_def]) >>
   qpat_x_assum `!op v. _ ==> ~MEM v future_outputs` irule >>
   qexists_tac `op` >> simp[]))
QED

(* Lower ownership and freshness at an indexed PHI boundary.  This does not
   assert physical upper support, nor distinctness of the whole stack. *)
Definition regional_selected_phi_inv_def:
  regional_selected_phi_inv lv dfg sb bb i ps <=>
    generated_plan_state_wf_marked sb ps /\
    (!phi. MEM phi (DROP i (collect_phis bb.bb_instructions)) ==>
      ?src. MEM (Var src) phi.inst_operands /\ MEM (Var src) ps.ps_stack /\
        (!v. MEM (Var v) phi.inst_operands /\
          (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src)) /\
    (!v. MEM v (live_vars_at lv bb.bb_label i) /\
      ~MEM (Var v) (FLAT (MAP (\phi. phi.inst_operands)
        (DROP i (collect_phis bb.bb_instructions)))) ==>
      MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
    (!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
      ~MEM op (FLAT (MAP (\phi. phi.inst_operands)
        (DROP i (collect_phis bb.bb_instructions)))) /\
      (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
      ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) (DROP i bb.bb_instructions))))
End

Theorem regional_lineage_selected_phi_inv:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps ==>
    regional_selected_phi_inv lv dfg sb bb 0 ps
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_static >> strip_tac >>
  pure_rewrite_tac[regional_selected_phi_inv_def, DROP_0] >>
  conj_tac >- simp[] >>
  conj_tac >-
    (rpt strip_tac >> drule_all regional_lineage_phi_depth >> metis_tac[]) >>
  metis_tac[]
QED

Theorem regional_lineage_phi_output_absent:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps phi out.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps /\ MEM phi (collect_phis bb.bb_instructions) /\
    MEM out phi.inst_outputs ==>
    ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lineage_state_static >> strip_tac >> gvs[] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `fn_reachable fn bb.bb_label` by
    (drule lineage_state_dfs_fields >> strip_tac >>
     drule_all dfs_block_state_cfg_reachable >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `~MEM (Var out) (FLAT (MAP (\p. p.inst_operands)
    (collect_phis bb.bb_instructions)))` by
    (strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
     rename1 `MEM usephi (collect_phis _)` >>
     `~MEM out (inst_uses usephi)` by
       metis_tac[regional_phi_output_not_phi_source] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `MEM out (FLAT (MAP (\p. p.inst_outputs) bb.bb_instructions))` by
    (simp[MEM_FLAT, MEM_MAP] >>
     qexists_tac `phi.inst_outputs` >> simp[] >>
     qexists_tac `phi` >> metis_tac[collect_phis_mem]) >>
  metis_tac[]
QED

Theorem regional_pop_singleton_slots_layout:
  plan_slots_bounded sb ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  plan_slots_bounded sb (SND (popmany_plan [v] ps)) /\
  spill_alloc_layout_wf (SND (popmany_plan [v] ps)).ps_alloc
    (SND (popmany_plan [v] ps)).ps_spilled
Proof
  strip_tac >> Cases_on `stack_get_depth v ps.ps_stack`
  >- simp[popmany_plan_def, popmany_individual_def, sortingTheory.QSORT_DEF,
          sortingTheory.PARTITION_DEF, sortingTheory.PART_DEF] >>
  rename1 `stack_get_depth v ps.ps_stack = SOME d` >>
  drule stack_get_depth_props >> strip_tac >>
  `plan_slots_bounded sb (SND (do_swap d ps))` by
    (irule do_swap_plan_slots_bounded >> metis_tac[PAIR]) >>
  drule_all do_swap_layout_wf >> strip_tac >>
  simp[popmany_plan_def, popmany_individual_def, is_contiguous_top_def,
       sortingTheory.QSORT_DEF, sortingTheory.PARTITION_DEF,
       sortingTheory.PART_DEF, LET_THM] >>
  Cases_on `d = 1`
  >- (gvs[do_swap_def, plan_slots_bounded_def] >> metis_tac[]) >>
  Cases_on `d = 0`
  >- (gvs[do_swap_def, plan_slots_bounded_def] >> metis_tac[]) >>
  gvs[] >> pairarg_tac >> gvs[plan_slots_bounded_def] >> metis_tac[]
QED

Theorem regional_selected_phi_slots_layout:
  generate_phi_plan phi nl halting ps = (ops,qs) /\
  phi.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
  stack_peek d ps.ps_stack = Var src /\ ~MEM src nl /\
  plan_slots_bounded sb ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  plan_slots_bounded sb qs /\ spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  strip_tac >>
  qpat_x_assum `generate_phi_plan _ _ _ _ = _` mp_tac >>
  simp[generate_phi_plan_def, LET_THM, stackPlanTypesTheory.operand_to_string_def] >>
  Cases_on `halting \/ MEM out nl`
  >- (simp[plan_slots_bounded_def] >> strip_tac >> gvs[plan_slots_bounded_def] >> metis_tac[]) >>
  simp[] >> pairarg_tac >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `popmany_plan [Var out] poked` >>
  `plan_slots_bounded sb poked /\
   spill_alloc_layout_wf poked.ps_alloc poked.ps_spilled` by
    (simp[Abbr `poked`, plan_slots_bounded_def] >>
     metis_tac[plan_slots_bounded_def]) >>
  drule_all regional_pop_singleton_slots_layout >>
  disch_then (qspec_then `Var out` mp_tac) >> gvs[]
QED

Theorem regional_selected_phi_wf:
  generate_phi_plan phi nl halting ps = (ops,qs) /\
  phi.inst_outputs = [out] /\
  stack_get_phi_depth (FILTER is_var_operand phi.inst_operands) ps.ps_stack = SOME d /\
  d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src /\
  ~MEM src nl /\ generated_plan_state_wf_marked sb ps /\
  ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled ==>
  generated_plan_state_wf_marked sb qs
Proof
  strip_tac >>
  `plan_slots_bounded sb ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
   ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack)` by
    gvs[generated_plan_state_wf_marked_def] >>
  drule_all regional_selected_phi_slots_layout >> strip_tac >>
  drule_all inventory_marked_phi_distinct >> strip_tac >>
  drule_all inventory_marked_phi_spilled >> strip_tac >>
  drule_all inventory_marked_phi_mem >> strip_tac >>
  gvs[generated_plan_state_wf_marked_def, pred_setTheory.IN_DISJOINT,
      pred_setTheory.IN_INTER, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem regional_selected_phi_output_absent:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv lv dfg sb bb i ps /\
  MEM out (EL i bb.bb_instructions).inst_outputs ==>
  ~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    metis_tac[collect_phis_index, EL_MEM] >>
  `~MEM (Var out) (FLAT (MAP (\p. p.inst_operands)
      (DROP i (collect_phis bb.bb_instructions))))` by
    (strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
     rename1 `MEM usephi (DROP i _)` >>
     `MEM usephi (collect_phis bb.bb_instructions)` by
       (drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
     `~MEM out (inst_uses usephi)` by
       metis_tac[regional_phi_output_not_phi_source] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `i < LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` current_collect_phis_length) >> decide_tac) >>
  `MEM out (FLAT (MAP (\p. p.inst_outputs) (DROP i bb.bb_instructions)))` by
    (simp[MEM_FLAT, MEM_MAP] >>
     qexists_tac `(EL i bb.bb_instructions).inst_outputs` >> simp[] >>
     qexists_tac `EL i bb.bb_instructions` >> metis_tac[DROP_CONS_EL, MEM]) >>
  gvs[regional_selected_phi_inv_def] >> metis_tac[]
QED

Theorem regional_selected_phi_next_coverage:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb i ps /\
  (EL i bb.bb_instructions).inst_outputs = [out] /\
  generate_phi_plan (EL i bb.bb_instructions)
    (live_vars_at (liveness_analyze fn) bb.bb_label (i+1)) halting ps = (ops,qs) /\
  stack_get_phi_depth (FILTER is_var_operand (EL i bb.bb_instructions).inst_operands)
    ps.ps_stack = SOME d /\ d < LENGTH ps.ps_stack /\
  stack_peek d ps.ps_stack = Var src /\
  MEM (Var src) (EL i bb.bb_instructions).inst_operands ==>
  !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (i+1)) /\
    ~MEM (Var v) (FLAT (MAP (\p. p.inst_operands)
      (DROP (i+1) (collect_phis bb.bb_instructions)))) ==>
    MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  strip_tac >>
  `~MEM src (live_vars_at (liveness_analyze fn) bb.bb_label (i+1))` by
    (irule regional_ready_phi_source_dead >> simp[] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `~MEM (Var out) ps.ps_stack` by metis_tac[regional_selected_phi_output_absent, MEM] >>
  `generated_plan_state_wf_marked sb ps` by gvs[regional_selected_phi_inv_def] >>
  drule_all regional_phi_owned_subtraction >> disch_tac >>
  qx_gen_tac `v` >> strip_tac >>
  Cases_on `v = out` >- metis_tac[] >>
  `~MEM v (inst_defs (EL i bb.bb_instructions))` by simp[inst_defs_def] >>
  `i < LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` current_collect_phis_length) >> decide_tac) >>
  `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
    (irule (SRULE [LET_THM] live_vars_at_propagate) >> simp[arithmeticTheory.ADD1] >>
     metis_tac[fn_reachable_in_cfg_dfs_pre, codegen_ready_fn_def]) >>
  `~MEM (Var v) (EL i bb.bb_instructions).inst_operands` by
    (strip_tac >>
     `MEM v (inst_uses (EL i bb.bb_instructions))` by
       gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
     metis_tac[regional_ready_phi_source_dead]) >>
  `DROP i (collect_phis bb.bb_instructions) =
    EL i bb.bb_instructions :: DROP (i+1) (collect_phis bb.bb_instructions)` by
    metis_tac[DROP_CONS_EL, collect_phis_index, arithmeticTheory.ADD1] >>
  gvs[regional_selected_phi_inv_def] >> metis_tac[]
QED

Theorem regional_indexed_phi_output:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) ==>
  ?out. (EL i bb.bb_instructions).inst_outputs = [out]
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    metis_tac[collect_phis_index, EL_MEM] >>
  `MEM (EL i bb.bb_instructions) bb.bb_instructions /\
   (EL i bb.bb_instructions).inst_opcode = PHI` by metis_tac[collect_phis_mem] >>
  `inst_wf (EL i bb.bb_instructions)` by
    (gvs[codegen_ready_fn_def, fn_inst_wf_def] >> metis_tac[]) >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute]
QED

Theorem regional_selected_phi_remaining:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv lv dfg sb bb i ps /\
  MEM (Var src) (EL i bb.bb_instructions).inst_operands /\
  MEM out (EL i bb.bb_instructions).inst_outputs /\
  qs.ps_spilled = ps.ps_spilled /\
  (!x. MEM x qs.ps_stack <=>
    (MEM x ps.ps_stack /\ x <> Var src) \/ (x = Var out /\ keep)) ==>
  !phi. MEM phi (DROP (i+1) (collect_phis bb.bb_instructions)) ==>
    ?v. MEM (Var v) phi.inst_operands /\ MEM (Var v) qs.ps_stack /\
      (!w. MEM (Var w) phi.inst_operands /\
        (MEM (Var w) qs.ps_stack \/ Var w IN FDOM qs.ps_spilled) ==> w = v)
Proof
  strip_tac >> qx_gen_tac `phi` >> disch_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    (drule_all ready_phi_block >> simp[phi_block_ready_def]) >>
  `MEM phi (collect_phis bb.bb_instructions)` by
    (drule rich_listTheory.MEM_DROP_IMP >> simp[]) >>
  `MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    metis_tac[collect_phis_index, EL_MEM] >>
  `~MEM (Var out) phi.inst_operands` by
    (strip_tac >>
     `~MEM out (inst_uses phi)` by metis_tac[regional_phi_output_not_phi_source] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `~MEM (Var src) phi.inst_operands` by
    (`?j. j < LENGTH (DROP (i+1) (collect_phis bb.bb_instructions)) /\
       EL j (DROP (i+1) (collect_phis bb.bb_instructions)) = phi` by
       metis_tac[MEM_EL] >>
     `i < j + (i+1) /\ j + (i+1) < LENGTH (collect_phis bb.bb_instructions)` by
       (gvs[LENGTH_DROP] >> decide_tac) >>
     `EL (j + (i+1)) (collect_phis bb.bb_instructions) = phi` by
       metis_tac[EL_DROP] >>
     `MEM src (inst_uses (EL i (collect_phis bb.bb_instructions)))` by
       metis_tac[collect_phis_index, inst_uses_def,
         passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
     drule_all regional_phi_later_uses >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `MEM phi (DROP i (collect_phis bb.bb_instructions))` by
    metis_tac[DROP_CONS_EL, collect_phis_index, MEM, arithmeticTheory.ADD1] >>
  `?v. MEM (Var v) phi.inst_operands /\ MEM (Var v) ps.ps_stack /\
    (!w. MEM (Var w) phi.inst_operands /\
      (MEM (Var w) ps.ps_stack \/ Var w IN FDOM ps.ps_spilled) ==> w = v)` by
    metis_tac[regional_selected_phi_inv_def] >>
  qexists_tac `v` >> conj_tac >- simp[] >>
  irule regional_phi_selected_frame >> simp[] >>
  qexistsl_tac [`out`, `keep`, `ps`, `src`] >> simp[] >> metis_tac[]
QED

Theorem regional_indexed_output_not_later:
  codegen_ready_fn fn /\ MEM bb fn.fn_blocks /\ i < LENGTH bb.bb_instructions /\
  MEM out (EL i bb.bb_instructions).inst_outputs ==>
  ~MEM out (FLAT (MAP (\p. p.inst_outputs) (DROP (i+1) bb.bb_instructions)))
Proof
  strip_tac >> strip_tac >> gvs[MEM_FLAT, MEM_MAP] >>
  rename1 `MEM later (DROP (i+1) bb.bb_instructions)` >>
  `?j. j < LENGTH (DROP (i+1) bb.bb_instructions) /\
    EL j (DROP (i+1) bb.bb_instructions) = later` by metis_tac[MEM_EL] >>
  `j + (i+1) < LENGTH bb.bb_instructions /\ i <> j + (i+1)` by
    (gvs[LENGTH_DROP] >> decide_tac) >>
  `EL (j + (i+1)) bb.bb_instructions = later` by metis_tac[EL_DROP] >>
  metis_tac[ready_output_other_location]
QED


Theorem regional_indexed_phi_freshness:
  regional_selected_phi_inv lv dfg sb bb i ps /\
  DROP i (collect_phis bb.bb_instructions) =
    phi :: DROP (i+1) (collect_phis bb.bb_instructions) /\
  DROP i bb.bb_instructions = phi :: DROP (i+1) bb.bb_instructions /\
  (!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src) /\
  (!op. (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) ==>
    op = Var out \/ ((MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\ op <> Var src)) /\
  ~MEM out (FLAT (MAP (\p. p.inst_outputs) (DROP (i+1) bb.bb_instructions))) /\
  normalize_operand dfg [] (Var out) = Var out ==>
  !op v. (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) /\
    ~MEM op (FLAT (MAP (\p. p.inst_operands)
      (DROP (i+1) (collect_phis bb.bb_instructions)))) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\p. p.inst_outputs) (DROP (i+1) bb.bb_instructions)))
Proof
  strip_tac >>
  `!op v. (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    ~MEM op (phi.inst_operands ++ FLAT (MAP (\p. p.inst_operands)
      (DROP (i+1) (collect_phis bb.bb_instructions)))) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\p. p.inst_outputs) (DROP (i+1) bb.bb_instructions)))` by
    (gvs[regional_selected_phi_inv_def] >> metis_tac[MEM]) >>
  rpt gen_tac >> strip_tac >>
  (Cases_on `op = Var out` >- gvs[] >>
   `(MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\ op <> Var src` by
     metis_tac[] >>
   (Cases_on `MEM op phi.inst_operands`
    >- (Cases_on `op` >> gvs[] >> metis_tac[normalize_operand_def]) >>
    qpat_x_assum `!op v. _ ==> ~MEM v _` irule >>
    qexists_tac `op` >> simp[]))
QED

Theorem regional_selected_phi_inv_step:
  !fn bb dfg sb i ps ops qs halting.
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfg = dfg_build_function fn /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb i ps /\
  generate_phi_plan (EL i bb.bb_instructions)
    (live_vars_at (liveness_analyze fn) bb.bb_label (i+1)) halting ps = (ops,qs) ==>
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb (i+1) qs
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    metis_tac[collect_phis_index, EL_MEM] >>
  `DROP i (collect_phis bb.bb_instructions) =
    EL i bb.bb_instructions :: DROP (i+1) (collect_phis bb.bb_instructions)` by
    metis_tac[DROP_CONS_EL, collect_phis_index, arithmeticTheory.ADD1] >>
  drule_all regional_indexed_phi_output >> strip_tac >>
  `?src. MEM (Var src) (EL i bb.bb_instructions).inst_operands /\
    MEM (Var src) ps.ps_stack /\
    (!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands /\
      (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src)` by
    (gvs[regional_selected_phi_inv_def] >> metis_tac[MEM]) >>
  `?d. stack_get_phi_depth
    (FILTER is_var_operand (EL i bb.bb_instructions).inst_operands) ps.ps_stack = SOME d /\
    d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src` by
    (irule regional_phi_physical_depth >> metis_tac[]) >>
  `~MEM src (live_vars_at (liveness_analyze fn) bb.bb_label (i+1))` by
    (irule regional_ready_phi_source_dead >> simp[] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `~MEM (Var out) ps.ps_stack /\ Var out NOTIN FDOM ps.ps_spilled` by
    metis_tac[regional_selected_phi_output_absent, MEM] >>
  `generated_plan_state_wf_marked sb ps /\
   ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack)` by
    gvs[regional_selected_phi_inv_def, generated_plan_state_wf_marked_def] >>
  drule_all inventory_marked_phi_mem >> disch_tac >>
  drule_all inventory_marked_phi_spilled >> disch_tac >>
  `MEM out (EL i bb.bb_instructions).inst_outputs` by simp[] >>
  mp_tac (Q.INST
    [`lv` |-> `liveness_analyze fn`,
     `keep` |-> `halting \/ MEM out (live_vars_at (liveness_analyze fn) bb.bb_label (i+1))`]
    (SPEC_ALL regional_selected_phi_remaining)) >>
  (impl_tac >- simp[]) >> disch_tac >>
  pure_rewrite_tac[regional_selected_phi_inv_def] >>
  conj_tac >- (irule regional_selected_phi_wf >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> irule regional_selected_phi_next_coverage >> metis_tac[]) >>
  `i < LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` current_collect_phis_length) >> decide_tac) >>
  `~MEM out (FLAT (MAP (\p. p.inst_outputs) (DROP (i+1) bb.bb_instructions)))` by
    metis_tac[regional_indexed_output_not_later] >>
  `normalize_operand dfg [] (Var out) = Var out` by
    metis_tac[regional_phi_output_normalize] >>
  `DROP i bb.bb_instructions = EL i bb.bb_instructions :: DROP (i+1) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL, arithmeticTheory.ADD1] >>
  drule_all regional_phi_owned_subtraction >> disch_tac >>
  `!op. (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) ==>
    op = Var out \/ ((MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\ op <> Var src)` by
    metis_tac[] >>
  mp_tac (Q.INST [`lv` |-> `liveness_analyze fn`,
    `phi` |-> `EL i bb.bb_instructions`] (SPEC_ALL regional_indexed_phi_freshness)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> simp[]
QED

Theorem regional_selected_phi_inv_prefix:
  !fn bb dfg cfg sb i j ps ops qs halting.
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfg = dfg_build_function fn /\
  i + j <= LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb i ps /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    halting 0 (LENGTH bb.bb_instructions) i j (DROP i bb.bb_instructions) ps =
      SOME (ops, qs) ==>
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb (i+j) qs
Proof
  Induct_on `j`
  >- simp[generate_block_insts_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  `i < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `i < LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` current_collect_phis_length) >> decide_tac) >>
  `DROP i bb.bb_instructions = EL i bb.bb_instructions :: DROP (i+1) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL, arithmeticTheory.ADD1] >>
  `(EL i bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[collect_phis_index, collect_phis_mem, EL_MEM] >>
  `DROP (i+1) bb.bb_instructions = [] ==> i+1 = LENGTH bb.bb_instructions` by
    (simp[DROP_EQ_NIL] >> decide_tac) >>
  `i+1 <= LENGTH bb.bb_instructions` by decide_tac >>
  `live_vars_at (liveness_analyze fn) bb.bb_label
    (if DROP (i+1) bb.bb_instructions = [] then LENGTH bb.bb_instructions else i+1) =
    live_vars_at (liveness_analyze fn) bb.bb_label (i+1)` by metis_tac[] >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_block_insts_prefix_def, generate_inst_plan_def,
    is_pre_codegen_opcode_def, LET_THM] >>
  simp[AllCaseEqs()] >> strip_tac >>
  `i+1 = LENGTH bb.bb_instructions \/ ~(LENGTH bb.bb_instructions <= i+1)` by decide_tac >>
  gvs[] >>
  rename1 `generate_phi_plan _ _ _ ps = (step_ops, mid)` >>
  `regional_selected_phi_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (i+1) mid` by
    (irule regional_selected_phi_inv_step >> simp[] >>
     qexistsl [`halting`, `step_ops`, `ps`] >> gvs[]) >>
  `i + SUC j = (i+1)+j` by decide_tac >>
  pop_assum SUBST1_TAC >> first_x_assum irule >> simp[] >>
  metis_tac[arithmeticTheory.ADD_CLAUSES, arithmeticTheory.ADD1]
QED

Theorem regional_selected_phi_inv_block_prefix:
  !fn bb dfg cfg sb j ps0 ops qs.
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfg = dfg_build_function fn /\
  LENGTH (get_params bb.bb_instructions) = 0 /\
  non_param_insts bb = bb.bb_instructions /\
  j <= LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb 0 ps0 /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
    (LENGTH bb.bb_instructions) 0 j (non_param_insts bb) ps0 =
      SOME (ops, qs) ==>
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb j qs
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`i` |-> `0`, `ps` |-> `ps0`, `halting` |-> `bb_is_halting bb`]
    (SPEC_ALL regional_selected_phi_inv_prefix)) >>
  gvs[]
QED

Theorem regional_phi_preparation_identity:
  !fn bb lv ps.
    codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    collect_phis bb.bb_instructions <> [] ==>
    (if bb = HD fn.fn_blocks then prepare_params_plan lv fn ps else ([],ps)) = ([],ps) /\
    (if LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1
     then clean_stack_plan lv (cfg_analyze fn) fn bb ps else ([],ps)) = ([],ps)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    (Cases_on `collect_phis bb.bb_instructions` >> gvs[] >>
     metis_tac[regional_phi_nonentry, MEM]) >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  `~(LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1)` by
    (gvs[codegen_ready_fn_def, phis_at_joins_def, EVERY_MEM, NULL_EQ] >>
     strip_tac >>
     qpat_x_assum `!bb'. MEM bb' _ ==> _` (qspec_then `bb` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem regional_selected_phi_inv_cleanup_fields:
  !lv dfg sb bb i ps h promised.
    regional_selected_phi_inv lv dfg sb bb i
      (ps with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) <=>
    regional_selected_phi_inv lv dfg sb bb i ps
Proof
  simp[regional_selected_phi_inv_def, generated_plan_state_wf_marked_def,
    plan_slots_bounded_def]
QED

Theorem regional_lineage_prepared_selected_phi_inv:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps_l h promised
    param_ops ps1 clean_ops ps2.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps_l /\ collect_phis bb.bb_instructions <> [] /\
    (if bb = HD fn.fn_blocks then prepare_params_plan lv fn
       (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([], ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (param_ops, ps1) /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan lv cfg fn bb ps1 else ([], ps1)) = (clean_ops, ps2) ==>
    regional_selected_phi_inv lv dfg sb bb 0 ps2
Proof
  rpt gen_tac >> strip_tac >>
  `regional_selected_phi_inv lv dfg sb bb 0 ps_l` by
    (drule_all regional_lineage_selected_phi_inv >> simp[]) >>
  drule_all regional_phi_preparation_identity >>
  disch_then (qspecl_then [`lv`,
    `ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`] mp_tac) >>
  strip_tac >> gvs[] >>
  drule_all regional_phi_preparation_identity >>
  disch_then (qspecl_then [`lv`, `ps1`] mp_tac) >>
  gvs[regional_selected_phi_inv_cleanup_fields]
QED

(* nonentry_block_no_params is downstream of the target, so cannot be imported. *)
Theorem regional_phi_no_params:
  !fn bb. codegen_ready_fn fn /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    collect_phis bb.bb_instructions <> [] ==>
    get_params bb.bb_instructions = [] /\
    non_param_insts bb = bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `fn_entry_label fn <> SOME bb.bb_label` by
    (Cases_on `collect_phis bb.bb_instructions` >> gvs[] >>
     metis_tac[regional_phi_nonentry, MEM]) >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def] >> metis_tac[]) >>
  `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
  `no_param_insts bb.bb_instructions` by
    (Cases_on `fn.fn_blocks` >> gvs[canonical_param_prefix_def, EVERY_MEM]) >>
  gvs[no_param_insts_def] >>
  conj_tac >- (Cases_on `bb.bb_instructions` >> gvs[get_params_def]) >>
  irule non_param_insts_all_neq >> simp[]
QED

Theorem regional_lineage_selected_phi_prefix:
  !lv dfg cfg ch growth sb ctr fn fn_ops ps_end bb ps_l h promised
    param_ops ps1 clean_ops ps2 j ops qs.
    lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
    cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
    generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
      SOME (fn_ops, ps_end) /\
    EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
      inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
      bb.bb_label ps_l /\ collect_phis bb.bb_instructions <> [] /\
    (if bb = HD fn.fn_blocks then prepare_params_plan lv fn
       (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)
     else ([], ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)) =
      (param_ops, ps1) /\
    (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1
     then clean_stack_plan lv cfg fn bb ps1 else ([], ps1)) = (clean_ops, ps2) /\
    j <= LENGTH (collect_phis bb.bb_instructions) /\
    generate_block_insts_prefix lv dfg cfg fn bb.bb_label
      (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
      (LENGTH bb.bb_instructions) 0 j (non_param_insts bb) ps2 = SOME (ops, qs) ==>
    regional_selected_phi_inv lv dfg sb bb j qs
Proof
  rpt gen_tac >> strip_tac >>
  `regional_selected_phi_inv lv dfg sb bb 0 ps2` by
    (drule_all regional_lineage_prepared_selected_phi_inv >> simp[]) >>
  `get_params bb.bb_instructions = [] /\
   non_param_insts bb = bb.bb_instructions` by
    (drule_all regional_phi_no_params >> simp[]) >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn_reachable fn bb.bb_label` by
    (drule lineage_state_dfs_fields >> strip_tac >> gvs[] >>
     drule_all dfs_block_state_cfg_reachable >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  gvs[] >>
  irule (INST_TYPE [alpha |-> ``:cfg_analysis``]
    regional_selected_phi_inv_block_prefix) >> simp[] >>
  qexistsl [`cfg_analyze fn`, `ops`, `ps2`] >> simp[]
QED

Theorem regional_selected_phi_exit_wf:
  !lv dfg sb bb ps.
    regional_selected_phi_inv lv dfg sb bb
      (LENGTH (collect_phis bb.bb_instructions)) ps ==>
    generated_plan_state_wf_marked sb ps
Proof
  simp[regional_selected_phi_inv_def]
QED

Theorem regional_selected_phi_exit_coverage:
  !lv dfg sb bb ps v.
    regional_selected_phi_inv lv dfg sb bb
      (LENGTH (collect_phis bb.bb_instructions)) ps /\
    MEM v (live_vars_at lv bb.bb_label (LENGTH (collect_phis bb.bb_instructions))) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled
Proof
  simp[regional_selected_phi_inv_def] >> metis_tac[]
QED

Theorem regional_selected_phi_exit_freshness:
  !lv dfg sb bb ps op v.
    regional_selected_phi_inv lv dfg sb bb
      (LENGTH (collect_phis bb.bb_instructions)) ps /\
    (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs)
      (DROP (LENGTH (collect_phis bb.bb_instructions)) bb.bb_instructions)))
Proof
  simp[regional_selected_phi_inv_def] >> metis_tac[]
QED

Theorem regional_emit_live_reserve:
  !opc inputs nl ps iops mid v.
    emit_input_plan opc inputs nl ps = (iops,mid) /\
    (!op. MEM op inputs /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    MEM v nl /\ (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
    LIST_ELEM_COUNT (Var v) inputs + 1 <=
      LIST_ELEM_COUNT (Var v) mid.ps_stack +
      (if Var v IN FDOM mid.ps_spilled then 1 else 0)
Proof
  rpt strip_tac >>
  qspecl_then [`inputs`,`opc`,`nl`,`ps`,`iops`,`mid`,`v`] mp_tac
    rf_emit_live_reserve >> simp[] >> strip_tac >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >>
  Cases_on `Var v IN FDOM ps.ps_spilled` >>
  Cases_on `Var v IN FDOM mid.ps_spilled` >> gvs[] >> decide_tac
QED

Theorem regional_live_input_residual:
  !inputs pending ps opc nl iops mid dfg rops arranged v.
    LENGTH inputs <= 16 /\ PERM pending inputs /\
    (!op. MEM op inputs /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    emit_input_plan opc inputs nl ps = (iops,mid) /\
    reorder_plan dfg pending mid = (rops,arranged) /\
    MEM v nl /\ MEM (Var v) inputs ==>
    MEM (Var v) (stack_pop (LENGTH inputs) arranged.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled` by
    (first_x_assum irule >> simp[is_var_operand_def]) >>
  `!x. LIST_ELEM_COUNT x pending = LIST_ELEM_COUNT x inputs` by
    (simp[LIST_ELEM_COUNT_DEF] >> metis_tac[PERM_FILTER, PERM_LENGTH]) >>
  `LENGTH pending = LENGTH inputs /\ MEM (Var v) pending` by
    metis_tac[PERM_LENGTH, PERM_MEM_EQ] >>
  `LENGTH pending <= LENGTH mid.ps_stack` by
    (drule available_input_plan_length >> simp[] >> metis_tac[]) >>
  `!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x mid.ps_stack` by
    (drule_all emit_input_plan_materialised >> simp[]) >>
  drule emit_input_plan_vars_not_spilled >>
  disch_then (qspec_then `Var v` assume_tac) >>
  drule regional_emit_live_reserve >>
  disch_then (qspec_then `v` mp_tac) >> simp[is_var_operand_def] >> strip_tac >>
  `!i. i < LENGTH pending ==>
    stack_peek (LENGTH pending - 1 - i) arranged.ps_stack = EL i pending` by
    metis_tac[reorder_plan_materialised_order] >>
  `LENGTH pending <= LENGTH arranged.ps_stack` by
    (irule reorder_plan_materialised_length_floor >> metis_tac[]) >>
  `LIST_ELEM_COUNT (Var v) arranged.ps_stack = LIST_ELEM_COUNT (Var v) mid.ps_stack` by
    metis_tac[reorder_plan_materialised_counts] >>
  `arranged.ps_stack = stack_pop (LENGTH pending) arranged.ps_stack ++ pending` by
    (irule fixed_suffix_decompose >> simp[]) >>
  `LIST_ELEM_COUNT (Var v) arranged.ps_stack =
   LIST_ELEM_COUNT (Var v) (stack_pop (LENGTH pending) arranged.ps_stack) +
   LIST_ELEM_COUNT (Var v) pending` by metis_tac[elem_count_append] >>
  gvs[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

Theorem regional_restore_ownership[local]:
  do_restore x ps = (ops,qs) /\
  (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
  MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled
Proof
  simp[do_restore_def] >> Cases_on `FLOOKUP ps.ps_spilled x` >>
  simp[stack_push_def, finite_mapTheory.FDOM_DOMSUB] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem regional_spill_tos_ownership[local]:
  0 < LENGTH ps.ps_stack /\ do_spill_tos ps = (ops,qs) /\
  (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
  MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled
Proof
  strip_tac >>
  `ps.ps_stack <> []` by (Cases_on `ps.ps_stack` >> gvs[]) >>
  `ps.ps_stack = SNOC (LAST ps.ps_stack) (FRONT ps.ps_stack)` by
    metis_tac[SNOC_LAST_FRONT] >>
  qpat_x_assum `do_spill_tos _ = _` mp_tac >>
  simp[do_spill_tos_def] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  once_asm_rewrite_tac[] >>
  simp[stack_pop_def, stack_peek_def, TAKE_SNOC, EL_LENGTH_SNOC,
       finite_mapTheory.FDOM_FUPDATE, MEM_SNOC] >> metis_tac[MEM_SNOC]
QED

Theorem regional_swap_ownership[local]:
  d < LENGTH ps.ps_stack /\ do_swap d ps = (ops,qs) /\
  (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
  MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled
Proof
  metis_tac[do_swap_stack_perm, do_swap_spilled_unchanged, PERM_MEM_EQ,
            pairTheory.SND]
QED

Theorem regional_stack_swap_membership[local]:
  d < LENGTH stk ==> (MEM op (stack_swap d stk) <=> MEM op stk)
Proof
  strip_tac >> simp[stack_swap_def, LET_THM] >>
  `LENGTH stk - 1 < LENGTH stk /\ LENGTH stk - (d + 1) < LENGTH stk` by decide_tac >>
  simp[MEM_EL, EL_LUPDATE] >> eq_tac >> rpt strip_tac
  >- (rpt (COND_CASES_TAC >> gvs[]) >> metis_tac[EL_MEM]) >>
  rename1 `op = EL i stk` >>
  Cases_on `i = LENGTH stk - 1`
  >- (qexists_tac `LENGTH stk - (d + 1)` >> simp[]) >>
  Cases_on `i = LENGTH stk - (d + 1)`
  >- (qexists_tac `LENGTH stk - 1` >> simp[] >> metis_tac[]) >>
  qexists_tac `i` >> simp[]
QED

Theorem regional_spill_ownership[local]:
  d < LENGTH ps.ps_stack /\ do_spill_at d ps = (ops,qs) /\
  (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
  MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled
Proof
  strip_tac >> Cases_on `d = 0`
  >- (gvs[do_spill_at_def] >> metis_tac[regional_spill_tos_ownership]) >>
  `!x. MEM x (stack_swap d ps.ps_stack) <=> MEM x ps.ps_stack` by
    metis_tac[regional_stack_swap_membership] >>
  qpat_x_assum `do_spill_at _ _ = _` mp_tac >>
  simp[do_spill_at_def, LET_THM] >>
  Cases_on `do_spill_tos (ps with ps_stack := stack_swap d ps.ps_stack)` >>
  simp[] >> strip_tac >> gvs[] >>
  irule regional_spill_tos_ownership >> goal_assum (drule_at Any) >>
  simp[]
QED

Theorem regional_reduce_ownership[local]:
  !fuel tops x f n ps ops qs op.
  reduce_depth_plan fuel tops x f n ps = (ops,qs) /\
  (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
  MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled
Proof
  Induct >- (simp[reduce_depth_plan_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> simp[reduce_depth_plan_def, LET_THM] >>
  Cases_on `f + 1 < n` >- (simp[] >> rpt strip_tac >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth x f n ps.ps_stack`
  >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth x f n ps.ps_stack = SOME dist` >>
  Cases_on `dist <= 16` >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack tops dist n`
  >- (simp[] >> rpt strip_tac >> gvs[]) >> simp[] >>
  rename1 `select_spill_candidate ps.ps_stack tops dist n = SOME cand` >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand < LENGTH ps.ps_stack` by
    (drule_all select_spill_candidate_bound >> simp[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >>
  metis_tac[regional_spill_ownership]
QED

Theorem regional_reorder_restore_ownership[local]:
  (case stack_get_unfixed_depth x f n ps.ps_stack of
     SOME _ => ([],ps)
   | NONE => case FLOOKUP ps.ps_spilled x of
       SOME _ => do_restore x ps | NONE => ([],ps)) = (ops,qs) ==>
  LENGTH ps.ps_stack <= LENGTH qs.ps_stack /\
  (!op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled ==>
        MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled)
Proof
  Cases_on `stack_get_unfixed_depth x f n ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled x` >> simp[] >> strip_tac >> gvs[] >>
  conj_tac
  >- (qpat_x_assum `do_restore _ _ = _` mp_tac >>
      simp[do_restore_def] >> strip_tac >> gvs[stack_push_def]) >>
  metis_tac[regional_restore_ownership]
QED

Theorem regional_reorder_reduce_ownership[local]:
  (if (dist:num) > 16 then reduce_depth_plan (LENGTH ps.ps_stack) pending x f
     (LENGTH pending) ps else ([],ps)) = (ops,qs) /\
  LENGTH pending <= 16 /\ LENGTH pending <= LENGTH ps.ps_stack ==>
  LENGTH pending <= LENGTH qs.ps_stack /\
  (!op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled ==>
        MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled)
Proof
  Cases_on `dist > 16` >> simp[] >> strip_tac >> gvs[] >>
  conj_tac >- (drule reduce_depth_plan_length_floor >> simp[] >> decide_tac) >>
  metis_tac[regional_reduce_ownership]
QED

Theorem regional_reorder_finish_ownership[local]:
  d < LENGTH ps.ps_stack /\ f < LENGTH ps.ps_stack /\
  stack_peek d ps.ps_stack = x /\
  (if d = f then (pre,ps)
   else if operand_equiv dfg x (stack_peek f ps.ps_stack) then
     (pre,ps with ps_stack := stack_poke f x
       (stack_poke d (stack_peek f ps.ps_stack) ps.ps_stack))
   else let (s1,mid) = do_swap d ps;
            (s2,last) = do_swap f mid in (pre ++ s1 ++ s2,last)) = (ops,qs) ==>
  LENGTH qs.ps_stack = LENGTH ps.ps_stack /\
  (!op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled ==>
        MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled)
Proof
  strip_tac >> Cases_on `d = f` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek d ps.ps_stack)
    (stack_peek f ps.ps_stack)` >> gvs[]
  >- (conj_tac >- simp[stack_poke_def] >>
      gen_tac >> strip_tac >> simp[] >>
      qspecl_then [`dfg`, `stack_peek d ps.ps_stack`, `d`, `f`, `ps`, `op`]
        mp_tac reorder_place_phase_multiplicity >> simp[] >>
      metis_tac[LIST_ELEM_COUNT_MEM]) >>
  Cases_on `do_swap d ps` >> gvs[] >>
  rename1 `do_swap d ps = (s1,mid)` >>
  Cases_on `do_swap f mid` >> gvs[] >>
  `LENGTH mid.ps_stack = LENGTH ps.ps_stack` by
    (qspec_then `d` (qspec_then `ps` mp_tac) do_swap_length >> simp[]) >>
  conj_tac >- (qspec_then `f` (qspec_then `mid` mp_tac) do_swap_length >> simp[]) >>
  metis_tac[regional_swap_ownership]
QED

Theorem regional_reorder_one_ownership[local]:
  LENGTH pending <= 16 /\ LENGTH pending <= LENGTH ps.ps_stack /\
  idx < LENGTH pending /\ reorder_one dfg pending idx x ps = (ops,qs) ==>
  LENGTH pending <= LENGTH qs.ps_stack /\
  (!op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled ==>
        MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled)
Proof
  strip_tac >> qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [reorder_one_def, LET_THM] >>
  `LENGTH pending - 1 - idx = LENGTH pending - (idx + 1)` by decide_tac >>
  asm_rewrite_tac[] >> pairarg_tac >>
  rename1 `(case stack_get_unfixed_depth _ _ _ _ of _ => _) = (restore_ops,mid)` >>
  `LENGTH pending <= LENGTH mid.ps_stack /\
   (!op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled ==>
         MEM op mid.ps_stack \/ op IN FDOM mid.ps_spilled)` by
    (drule regional_reorder_restore_ownership >> strip_tac >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `stack_get_unfixed_depth x (LENGTH pending - (idx + 1))
    (LENGTH pending) mid.ps_stack` >> simp[]
  >- (strip_tac >> gvs[] >> first_assum ACCEPT_TAC) >>
  pairarg_tac >>
  rename1 `(if _ then reduce_depth_plan _ _ _ _ _ _ else _) = (reduce_ops,last)` >>
  `LENGTH pending <= LENGTH last.ps_stack /\
   (!op. MEM op mid.ps_stack \/ op IN FDOM mid.ps_spilled ==>
         MEM op last.ps_stack \/ op IN FDOM last.ps_spilled)` by
    (drule regional_reorder_reduce_ownership >> simp[] >> metis_tac[]) >>
  Cases_on `stack_get_unfixed_depth x (LENGTH pending - (idx + 1))
    (LENGTH pending) last.ps_stack` >> simp[]
  >- (strip_tac >> gvs[] >> metis_tac[]) >>
  rename1 `stack_get_unfixed_depth x _ _ last.ps_stack = SOME depth` >>
  `depth < LENGTH last.ps_stack /\ stack_peek depth last.ps_stack = x` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH pending - (idx + 1) < LENGTH last.ps_stack` by decide_tac >>
  simp[] >> strip_tac >>
  drule_all (SRULE[LET_THM, APPEND_ASSOC] regional_reorder_finish_ownership) >> strip_tac >>
  conj_tac >- decide_tac >> metis_tac[]
QED

Theorem regional_reorder_steps_ownership[local]:
  !items ps ops qs pending dfg.
  EVERY (\(idx,x). idx < LENGTH pending) items /\
  LENGTH pending <= 16 /\ LENGTH pending <= LENGTH ps.ps_stack /\
  plan_steps (\(idx,x) ps. reorder_one dfg pending idx x ps) items ps = (ops,qs) ==>
  LENGTH pending <= LENGTH qs.ps_stack /\
  (!op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled ==>
        MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled)
Proof
  Induct >- (simp[foldlSimTheory.plan_steps_def] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[foldlSimTheory.plan_steps_def] >> strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `reorder_one dfg pending idx x ps = (step_ops,mid)` >>
  `LENGTH pending <= LENGTH mid.ps_stack /\
   (!op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled ==>
         MEM op mid.ps_stack \/ op IN FDOM mid.ps_spilled)` by
    (drule_all regional_reorder_one_ownership >> metis_tac[]) >>
  first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem regional_reorder_materialised_ownership:
  !dfg pending mid rops arranged op.
  LENGTH pending <= 16 /\ LENGTH pending <= LENGTH mid.ps_stack /\
  (!x. MEM x pending ==> LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x mid.ps_stack) /\
  reorder_plan dfg pending mid = (rops,arranged) /\
  (MEM op mid.ps_stack \/ op IN FDOM mid.ps_spilled) ==>
  MEM op arranged.ps_stack \/ op IN FDOM arranged.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\(idx,x). idx < LENGTH pending) (MAPi (\i x. (i,x)) pending)` by
    simp[EVERY_EL, indexedListsTheory.LENGTH_MAPi, indexedListsTheory.EL_MAPi] >>
  gvs[reorder_plan_eq_plan_steps] >>
  drule_all regional_reorder_steps_ownership >> metis_tac[]
QED

Theorem regional_live_ownership_residual:
  !inputs pending ps opc nl iops mid dfg rops arranged v.
    LENGTH inputs <= 16 /\ PERM pending inputs /\
    (!op. MEM op inputs /\ is_var_operand op ==>
      MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    emit_input_plan opc inputs nl ps = (iops,mid) /\
    reorder_plan dfg pending mid = (rops,arranged) /\
    MEM v nl /\ (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
    MEM (Var v) (stack_pop (LENGTH inputs) arranged.ps_stack) \/
    Var v IN FDOM arranged.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  (Cases_on `MEM (Var v) inputs`
   >- (disj1_tac >> irule regional_live_input_residual >> metis_tac[])) >>
  `LENGTH pending = LENGTH inputs /\ ~MEM (Var v) pending` by
    metis_tac[PERM_LENGTH, PERM_MEM_EQ] >>
  `!x. LIST_ELEM_COUNT x pending = LIST_ELEM_COUNT x inputs` by
    (simp[LIST_ELEM_COUNT_DEF] >> metis_tac[PERM_FILTER, PERM_LENGTH]) >>
  `LENGTH pending <= LENGTH mid.ps_stack` by
    (drule available_input_plan_length >> simp[] >> metis_tac[]) >>
  `!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x mid.ps_stack` by
    (drule_all emit_input_plan_materialised >> simp[]) >>
  `MEM (Var v) mid.ps_stack \/ Var v IN FDOM mid.ps_spilled` by
    (drule regional_emit_live_reserve >>
     disch_then (qspec_then `v` mp_tac) >> simp[] >>
     Cases_on `Var v IN FDOM mid.ps_spilled` >>
     gvs[GSYM LIST_ELEM_COUNT_MEM]) >>
  `MEM (Var v) arranged.ps_stack \/ Var v IN FDOM arranged.ps_spilled` by
    (irule regional_reorder_materialised_ownership >> metis_tac[]) >>
  `!i. i < LENGTH pending ==>
    stack_peek (LENGTH pending - 1 - i) arranged.ps_stack = EL i pending` by
    metis_tac[reorder_plan_materialised_order] >>
  `LENGTH pending <= LENGTH arranged.ps_stack` by
    (irule reorder_plan_materialised_length_floor >> metis_tac[]) >>
  `arranged.ps_stack = stack_pop (LENGTH pending) arranged.ps_stack ++ pending` by
    (irule fixed_suffix_decompose >> simp[]) >>
  metis_tac[MEM_APPEND]
QED

Theorem regional_optimistic_ownership[local]:
  !dfg inst nl nt ps op.
  MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled ==>
  MEM op (SND (optimistic_swap_plan dfg inst nl nt ps)).ps_stack \/
  op IN FDOM (SND (optimistic_swap_plan dfg inst nl nt ps)).ps_spilled
Proof
  rpt gen_tac >> strip_tac >> simp[optimistic_swap_plan_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >> simp[] >>
  rename1 `stack_get_depth _ _ = SOME dist` >>
  drule stack_get_depth_props >> strip_tac >>
  simp[do_swap_stack_result, do_swap_spilled_unchanged,
       regional_stack_swap_membership]
QED

Theorem regional_dead_outputs_owned[local]:
  !outputs nl ps v.
  ALL_DISTINCT ps.ps_stack /\ MEM v nl /\
  (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
  MEM (Var v) (SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) outputs)) ps)).ps_stack \/
  Var v IN FDOM (SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) outputs)) ps)).ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  drule inventory_popmany >>
  disch_then (qspec_then `MAP Var (FILTER (\v. ~MEM v nl) outputs)` mp_tac) >>
  simp[MEM_MAP, MEM_FILTER, rf_popmany_spilled] >> metis_tac[]
QED

Theorem regional_regular_live_coverage:
  !inst sb ps lv dfg cfg fn nl halting next_term lbl ops qs v.
  inst.inst_opcode <> JMP /\
  plan_slots_bounded sb ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  ALL_DISTINCT ps.ps_stack /\
  DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  ALL_DISTINCT inst.inst_outputs /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    inst.inst_outputs /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = (ops,qs) /\
  MEM v nl /\
  (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/ MEM v inst.inst_outputs)
  ==>
  MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `emit_input_plan _ _ _ _ = (iops,mid)` >>
  rename1 `_ = (rops,arranged)` >>
  `?pending. PERM pending (compute_operands inst) /\
    reorder_plan dfg pending mid = (rops,arranged)` by
    (irule inventory_selected_reorder >> qexists_tac `inst.inst_opcode` >> simp[LET_THM]) >>
  qpat_x_assum `(if _ then _ else _) = (rops,arranged)` kall_tac >> fs[] >>
  `LENGTH (compute_operands inst) <= LENGTH mid.ps_stack` by
    (drule available_input_plan_length >> simp[] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics pushed` >>
  `ALL_DISTINCT pushed.ps_stack /\ DISJOINT (set pushed.ps_stack) (FDOM pushed.ps_spilled)` by
    (irule inventory_regular_output_resources >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
     simp[Abbr `pushed`] >> metis_tac[]) >>
  `MEM (Var v) pushed.ps_stack \/ Var v IN FDOM pushed.ps_spilled` by
    (simp[Abbr `pushed`, inventory_output_push_stack, inventory_output_push_spilled] >>
     Cases_on `MEM v inst.inst_outputs` >- simp[MEM_MAP] >>
     `MEM (Var v) (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack) \/
      Var v IN FDOM arranged.ps_spilled` by
       (irule regional_live_ownership_residual >> metis_tac[]) >> simp[]) >>
  pairarg_tac >> simp[] >>
  rename1 `generate_emit_ops _ _ _ = (eops,emitted)` >>
  `ALL_DISTINCT emitted.ps_stack /\
   (MEM (Var v) emitted.ps_stack \/ Var v IN FDOM emitted.ps_spilled)` by
    metis_tac[fnBlockPlanStaticBalanceTheory.generate_emit_ops_stack, inventory_emit_ops_spilled, pairTheory.SND] >>
  qpat_x_assum `Abbrev (topics = _)` kall_tac >>
  qpat_x_assum `Abbrev (pushed = _)` kall_tac >>
  (Cases_on `inst.inst_outputs = []`
  >- (simp[] >> strip_tac >> gvs[] >> metis_tac[rf_release_live_owned, release_dead_spills_stack]) >>
  `MEM (Var v) (SND (if ~halting \/ LENGTH inst.inst_outputs > 1 then
      popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) emitted
      else ([],emitted))).ps_stack \/
   Var v IN FDOM (SND (if ~halting \/ LENGTH inst.inst_outputs > 1 then
      popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) emitted
      else ([],emitted))).ps_spilled` by
    (IF_CASES_TAC >> simp[] >> irule regional_dead_outputs_owned >> simp[]) >>
  simp[] >> pairarg_tac >> fs[] >> pairarg_tac >> simp[] >>
  rename1 `_ = (oopt,optimised)` >>
  `MEM (Var v) optimised.ps_stack \/ Var v IN FDOM optimised.ps_spilled` by
    (Cases_on `FILTER (\out. MEM out nl) inst.inst_outputs = []` >> gvs[] >>
     metis_tac[regional_optimistic_ownership, pairTheory.SND]) >>
  strip_tac >> gvs[] >> metis_tac[rf_release_live_owned, release_dead_spills_stack])
QED

Theorem regional_indexed_regular_live_coverage:
  !fn bb i inst sb ps dfg cfg halting nt ops qs.
  wf_function fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> OFFSET /\
  inst.inst_opcode <> NOP /\ inst.inst_opcode <> JMP /\
  ~is_param_opcode inst.inst_opcode /\
  plan_slots_bounded sb ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  ALL_DISTINCT ps.ps_stack /\ DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  ALL_DISTINCT inst.inst_outputs /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    inst.inst_outputs /\
  (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
  generate_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halting nt
    bb.bb_label ps = SOME (ops,qs) ==>
  !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
    MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `generate_inst_plan _ _ _ _ _ _ halting next_term _ _ = _` >>
  qx_gen_tac `v` >> disch_tac >>
  `generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halting next_term
    bb.bb_label ps = (ops,qs)` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, LET_THM] >> rpt IF_CASES_TAC >> gvs[]) >>
  `MEM v inst.inst_outputs \/
   MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
    (Cases_on `MEM v inst.inst_outputs` >- simp[] >>
     disj2_tac >> irule (SRULE[LET_THM, inst_defs_def] live_vars_at_propagate) >>
     metis_tac[]) >>
  irule regional_regular_live_coverage >>
  goal_assum (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `sb` >> simp[] >> metis_tac[]
QED

Theorem regional_indexed_special_live_coverage:
  !fn bb i inst ps dfg cfg halting next_term ops qs.
  wf_function fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  inst_wf inst /\ (inst.inst_opcode = NOP \/ inst.inst_opcode = OFFSET) /\
  (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
  generate_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halting next_term
    bb.bb_label ps = SOME (ops,qs) ==>
  !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
    MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `v` >> disch_tac >>
  `MEM v inst.inst_outputs \/
   MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
    (Cases_on `MEM v inst.inst_outputs` >- simp[] >>
     disj2_tac >> irule (SRULE[LET_THM, inst_defs_def] live_vars_at_propagate) >>
     metis_tac[]) >>
  (Cases_on `inst.inst_opcode = NOP`
   >- (gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def] >>
       gvs[inst_wf_def] >> metis_tac[]) >>
   `inst.inst_opcode = OFFSET` by metis_tac[] >>
   drule_all inst_wf_offset_shape >> strip_tac >>
   gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
       generate_offset_plan_def, stack_push_def] >> metis_tac[])
QED

Theorem regional_indexed_body_live_coverage:
  !fn bb i inst sb ps dfg cfg halting next_term ops qs.
  wf_function fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
  ~is_param_opcode inst.inst_opcode /\
  plan_slots_bounded sb ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  ALL_DISTINCT ps.ps_stack /\ DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  ALL_DISTINCT inst.inst_outputs /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    inst.inst_outputs /\
  (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
  generate_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halting next_term
    bb.bb_label ps = SOME (ops,qs) ==>
  !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
    MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `v` >> disch_tac >>
  Cases_on `inst.inst_opcode = NOP \/ inst.inst_opcode = OFFSET`
  >- (irule regional_indexed_special_live_coverage >>
      goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
      simp[] >> metis_tac[]) >>
  irule regional_indexed_regular_live_coverage >>
  goal_assum (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `sb` >> simp[] >> metis_tac[]
QED

Theorem regional_regular_resources:
  inst.inst_opcode <> JMP /\
  plan_slots_bounded sb ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  ALL_DISTINCT ps.ps_stack /\ DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  ALL_DISTINCT inst.inst_outputs /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    inst.inst_outputs /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = (ops,qs) ==>
  ALL_DISTINCT qs.ps_stack /\ DISJOINT (set qs.ps_stack) (FDOM qs.ps_spilled)
Proof
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `emit_input_plan _ _ _ _ = (iops,mid)` >>
  rename1 `_ = (rops,arranged)` >>
  `?pending. PERM pending (compute_operands inst) /\
    reorder_plan dfg pending mid = (rops,arranged)` by
    (irule inventory_selected_reorder >> qexists_tac `inst.inst_opcode` >> simp[LET_THM]) >>
  qpat_x_assum `(if _ then _ else _) = (rops,arranged)` kall_tac >> fs[] >>
  `LENGTH (compute_operands inst) <= LENGTH mid.ps_stack` by
    (drule available_input_plan_length >> simp[] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics pushed` >>
  `ALL_DISTINCT pushed.ps_stack /\ DISJOINT (set pushed.ps_stack) (FDOM pushed.ps_spilled)` by
    (irule inventory_regular_output_resources >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
     simp[Abbr `pushed`] >> metis_tac[]) >>
  pairarg_tac >> simp[] >>
  rename1 `generate_emit_ops _ _ _ = (eops,emitted)` >>
  `ALL_DISTINCT emitted.ps_stack /\ DISJOINT (set emitted.ps_stack) (FDOM emitted.ps_spilled)` by
    metis_tac[fnBlockPlanStaticBalanceTheory.generate_emit_ops_stack, inventory_emit_ops_spilled, pairTheory.SND] >>
  qpat_x_assum `Abbrev (topics = _)` kall_tac >>
  qpat_x_assum `Abbrev (pushed = _)` kall_tac >>
  Cases_on `inst.inst_outputs = []`
  >- (simp[] >> strip_tac >> gvs[] >>
      metis_tac[inventory_release_resources, release_dead_spills_stack]) >>
  `ALL_DISTINCT (SND (if ~halting \/ LENGTH inst.inst_outputs > 1 then
      popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) emitted
      else ([],emitted))).ps_stack /\
   DISJOINT (set (SND (if ~halting \/ LENGTH inst.inst_outputs > 1 then
      popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) emitted
      else ([],emitted))).ps_stack)
     (FDOM (SND (if ~halting \/ LENGTH inst.inst_outputs > 1 then
      popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) emitted
      else ([],emitted))).ps_spilled)` by
    (IF_CASES_TAC >> simp[] >> irule inventory_popmany_resources >> simp[]) >>
  simp[] >> pairarg_tac >> fs[] >> pairarg_tac >> simp[] >>
  rename1 `_ = (oopt,optimised)` >>
  `ALL_DISTINCT optimised.ps_stack /\ DISJOINT (set optimised.ps_stack) (FDOM optimised.ps_spilled)` by
    (Cases_on `FILTER (\out. MEM out nl) inst.inst_outputs = []` >> gvs[] >>
     metis_tac[inventory_optimistic_swap_resources, pairTheory.SND]) >>
  strip_tac >> gvs[] >>
  metis_tac[inventory_release_resources, release_dead_spills_stack]
QED

Theorem regional_body_resources:
  inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
  ~is_param_opcode inst.inst_opcode /\
  plan_slots_bounded sb ps /\ spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
  ALL_DISTINCT ps.ps_stack /\ DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  ALL_DISTINCT inst.inst_outputs /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    inst.inst_outputs /\
  generate_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = SOME (ops,qs) ==>
  ALL_DISTINCT qs.ps_stack /\ DISJOINT (set qs.ps_stack) (FDOM qs.ps_spilled)
Proof
  strip_tac >>
  Cases_on `inst.inst_opcode = NOP`
  >- gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def] >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (drule_all inst_wf_offset_shape >> strip_tac >>
      gvs[generate_inst_plan_def, is_pre_codegen_opcode_def, is_param_opcode_def,
          generate_offset_plan_def, stack_push_def, EVERY_DEF, ALL_DISTINCT_SNOC,
          pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `generate_regular_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = (ops,qs)` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, LET_THM] >> rpt IF_CASES_TAC >> gvs[]) >>
  irule regional_regular_resources >>
  goal_assum (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `sb` >> simp[]
QED

Theorem regional_optimistic_stack_membership[local]:
  MEM op (SND (optimistic_swap_plan dfg inst nl next_term ps)).ps_stack <=>
  MEM op ps.ps_stack
Proof
  simp[optimistic_swap_plan_def, LET_THM] >> rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >> simp[] >>
  rename1 `stack_get_depth _ _ = SOME dist` >>
  drule stack_get_depth_props >> strip_tac >>
  simp[do_swap_stack_result, regional_stack_swap_membership]
QED

Theorem regional_params_exact_filter[local]:
  ALL_DISTINCT installed.ps_stack /\
  installed.ps_stack = MAP (\i. Var (HD i.inst_outputs)) params /\
  installed.ps_spilled = FEMPTY /\
  popmany_plan (FILTER is_var_operand
    (FILTER (\v. ~MEM (operand_to_string v) nl) installed.ps_stack)) installed = (ops,mid) /\
  optimistic_swap_plan dfg inst nl next_term mid = (swaps,qs) ==>
  ALL_DISTINCT qs.ps_stack /\ qs.ps_spilled = FEMPTY /\
  (!op. MEM op qs.ps_stack <=>
    MEM op installed.ps_stack /\ MEM (operand_to_string op) nl)
Proof
  strip_tac >>
  `ALL_DISTINCT mid.ps_stack` by metis_tac[inventory_popmany_distinct] >>
  `mid.ps_spilled = FEMPTY` by
    metis_tac[fnFrameStepsRevertForwardTheory.rf_popmany_spilled, pairTheory.SND] >>
  drule inventory_optimistic_swap_resources >> simp[] >> strip_tac >>
  `qs.ps_spilled = FEMPTY` by
    metis_tac[fnFrameStepsRevertForwardTheory.rf_optimistic_spilled, pairTheory.SND] >>
  `ALL_DISTINCT qs.ps_stack` by metis_tac[pairTheory.SND] >>
  simp[] >> gen_tac >>
  `MEM op qs.ps_stack <=> MEM op mid.ps_stack` by
    metis_tac[regional_optimistic_stack_membership, pairTheory.SND] >>
  drule_all inventory_popmany_mem >>
  disch_then (qspec_then `op` assume_tac) >>
  Cases_on `MEM op installed.ps_stack`
  >- (`is_var_operand op` by
        (gvs[MEM_MAP] >> simp[stackPlanTypesTheory.is_var_operand_def]) >>
      gvs[MEM_FILTER]) >>
  gvs[MEM_FILTER]
QED

Theorem regional_prepare_params_initial_exact[local]:
  codegen_ready_fn fn /\
  prepare_params_plan (liveness_analyze fn) fn
    ((init_cleanup_plan_state ch growth sb ctr) with
      <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) = (ops,qs) ==>
  ALL_DISTINCT qs.ps_stack /\ qs.ps_spilled = FEMPTY /\
  (!op. MEM op qs.ps_stack <=>
    MEM op (MAP (\i. Var (HD i.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions)) /\
    MEM (operand_to_string op)
      (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))))
Proof
  strip_tac >>
  qpat_x_assum `prepare_params_plan _ _ _ = _` mp_tac >>
  simp[prepare_params_plan_def, LET_THM] >>
  qmatch_goalsub_abbrev_tac `get_params entry.bb_instructions` >>
  Cases_on `get_params entry.bb_instructions = []`
  >- (strip_tac >> gvs[init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def]) >>
  simp[parameter_stack_fold] >>
  qmatch_goalsub_abbrev_tac `popmany_plan items installed` >>
  pairarg_tac >> simp[] >>
  rename1 `popmany_plan items installed = (pops,mid)` >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `ALL_DISTINCT installed.ps_stack` by
    (simp[Abbr `installed`] >> metis_tac[regional_param_heads_distinct]) >>
  `installed.ps_spilled = FEMPTY` by
    simp[Abbr `installed`, init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def] >>
  `installed.ps_stack = MAP (\i. Var (HD i.inst_outputs))
      (get_params entry.bb_instructions)` by simp[Abbr `installed`] >>
  `popmany_plan (FILTER is_var_operand
      (FILTER (\v. ~MEM (operand_to_string v)
        (live_vars_at (liveness_analyze fn) entry.bb_label
          (LENGTH (get_params entry.bb_instructions)))) installed.ps_stack))
      installed = (pops,mid)` by gvs[Abbr `items`] >>
  drule_all regional_params_exact_filter >> simp[]
QED

Theorem regional_prepare_params_initial_membership:
  codegen_ready_fn fn /\
  prepare_params_plan (liveness_analyze fn) fn
    ((init_cleanup_plan_state ch growth sb ctr) with
      <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) = (ops,qs) ==>
  !op. MEM op qs.ps_stack <=>
    MEM op (MAP (\i. Var (HD i.inst_outputs))
      (get_params (HD fn.fn_blocks).bb_instructions)) /\
    MEM (operand_to_string op)
      (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
        (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))
Proof
  strip_tac >> drule_all regional_prepare_params_initial_exact >> simp[]
QED

Theorem regional_prepare_params_initial_spilled:
  codegen_ready_fn fn /\
  prepare_params_plan (liveness_analyze fn) fn
    ((init_cleanup_plan_state ch growth sb ctr) with
      <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) = (ops,qs) ==>
  qs.ps_spilled = FEMPTY
Proof
  strip_tac >> drule_all regional_prepare_params_initial_exact >> simp[]
QED

Theorem regional_prepare_params_initial_distinct:
  codegen_ready_fn fn /\
  prepare_params_plan (liveness_analyze fn) fn
    ((init_cleanup_plan_state ch growth sb ctr) with
      <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) = (ops,qs) ==>
  ALL_DISTINCT qs.ps_stack
Proof
  strip_tac >> drule_all regional_prepare_params_initial_exact >> simp[]
QED


Theorem regional_entry_no_phi[local]:
  codegen_ready_fn fn /\ j < LENGTH (HD fn.fn_blocks).bb_instructions ==>
  (EL j (HD fn.fn_blocks).bb_instructions).inst_opcode <> PHI
Proof
  strip_tac >> drule_all regional_entry_structure >> strip_tac >>
  `(EL 0 (HD fn.fn_blocks).bb_instructions).inst_opcode <> PHI` by
    (Cases_on `(HD fn.fn_blocks).bb_instructions` >>
     gvs[livenessDefsTheory.collect_phis_def] >> rename1 `if head_inst.inst_opcode = PHI then _ else _` >>
     Cases_on `head_inst.inst_opcode = PHI` >> gvs[]) >>
  Cases_on `j = 0` >- gvs[] >>
  gvs[bb_well_formed_def] >>
  qpat_x_assum `!i j. _` (qspecl_then [`0`,`j`] mp_tac) >> simp[]
QED

Theorem regional_entry_params_live_heads:
  codegen_ready_fn fn /\
  MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
  MEM (Var v) (MAP (\i. Var (HD i.inst_outputs))
    (get_params (HD fn.fn_blocks).bb_instructions))
Proof
  strip_tac >> drule_all regional_entry_structure >> strip_tac >>
  qspec_then `(HD fn.fn_blocks).bb_instructions` strip_assume_tac get_params_suffix >>
  `LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <=
    LENGTH (HD fn.fn_blocks).bb_instructions` by metis_tac[LENGTH_APPEND, arithmeticTheory.LE_ADD] >>
  `!j. LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <= j /\
    j < LENGTH (HD fn.fn_blocks).bb_instructions /\
    (EL j (HD fn.fn_blocks).bb_instructions).inst_opcode = PHI ==>
    ~MEM (Var v) (EL j (HD fn.fn_blocks).bb_instructions).inst_operands` by
    metis_tac[regional_entry_no_phi] >>
  drule_all fnLiveDefDomTheory.live_def_dominates >> strip_tac >>
  `def_bb.bb_label = (HD fn.fn_blocks).bb_label` by
    metis_tac[dominates_entry_label] >>
  first_x_assum (drule_then strip_assume_tac) >>
  `MEM def_inst (get_params (HD fn.fn_blocks).bb_instructions)` by
    metis_tac[EL_APPEND1, EL_MEM] >>
  `param_insts_from 0 (get_params (HD fn.fn_blocks).bb_instructions)` by
    (irule (cj 1 canonical_get_params_layout) >> qexists_tac `fn` >> simp[]) >>
  drule param_insts_flat_outputs >> strip_tac >>
  `MEM v (MAP (\i. HD i.inst_outputs) (get_params (HD fn.fn_blocks).bb_instructions))` by
    metis_tac[MEM_FLAT, MEM_MAP] >>
  gvs[MEM_MAP] >> metis_tac[]
QED

Theorem regional_prepare_params_initial_live_coverage:
  codegen_ready_fn fn /\
  prepare_params_plan (liveness_analyze fn) fn
    ((init_cleanup_plan_state ch growth sb ctr) with
      <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) = (ops,qs) ==>
  !v. MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
    (LENGTH (get_params (HD fn.fn_blocks).bb_instructions))) ==>
      MEM (Var v) qs.ps_stack
Proof
  strip_tac >> drule_all regional_prepare_params_initial_membership >>
  strip_tac >> rpt strip_tac >>
  `MEM (Var v) (MAP (\i. Var (HD i.inst_outputs))
    (get_params (HD fn.fn_blocks).bb_instructions))` by
    metis_tac[regional_entry_params_live_heads] >>
  gvs[stackPlanTypesTheory.operand_to_string_def]
QED

Theorem regional_filter_take_distinct[local]:
  !xs n. ALL_DISTINCT (FILTER P xs) ==>
    ALL_DISTINCT (FILTER P (TAKE n xs))
Proof
  Induct >> simp[] >> Cases_on `n` >> simp[] >>
  Cases_on `P h` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[MEM_TAKE, MEM_FILTER]
QED

Theorem regional_perm_pop_inventory[local]:
  PERM ys xs /\ ALL_DISTINCT (FILTER P xs) ==>
  ALL_DISTINCT (FILTER P (stack_pop n ys)) /\
  (!op. MEM op (stack_pop n ys) ==> MEM op xs)
Proof
  strip_tac >>
  `ALL_DISTINCT (FILTER P ys)` by
    metis_tac[PERM_FILTER, ALL_DISTINCT_PERM] >>
  conj_tac
  >- (simp[stack_pop_def] >> irule regional_filter_take_distinct >> simp[]) >>
  simp[stack_pop_def] >> metis_tac[MEM_TAKE, PERM_MEM_EQ]
QED

Theorem regional_popmany_fold_marked_inventory[local]:
  !xs acc ps.
  ALL_DISTINCT (FILTER P ps.ps_stack) ==>
  let qs = SND (FOLDL (\(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
          let (swap_ops, qs) =
            if dist = 0 then ([], ps) else do_swap dist ps in
          (ops ++ swap_ops ++ [SOPop 1],
           qs with ps_stack := stack_pop 1 qs.ps_stack)) (acc,ps) xs) in
  ALL_DISTINCT (FILTER P qs.ps_stack) /\
  (!op. MEM op qs.ps_stack ==> MEM op ps.ps_stack)
Proof
  Induct >> simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  fs[LET_THM] >> Cases_on `stack_get_depth h ps.ps_stack`
  >- (first_x_assum (qspecl_then [`acc`, `ps`] mp_tac) >> simp[]) >>
  rename1 `stack_get_depth h ps.ps_stack = SOME d` >>
  drule stack_get_depth_props >> strip_tac >>
  `PERM (SND (do_swap d ps)).ps_stack ps.ps_stack` by
    (irule do_swap_stack_perm >> simp[]) >>
  Cases_on `d = 0`
  >- (simp[] >>
      `ALL_DISTINCT (FILTER P (stack_pop 1 ps.ps_stack)) /\
       (!op. MEM op (stack_pop 1 ps.ps_stack) ==> MEM op ps.ps_stack)` by
        (irule regional_perm_pop_inventory >> simp[]) >>
      first_x_assum (qspecl_then [`acc ++ [SOPop 1]`,
        `ps with ps_stack := stack_pop 1 ps.ps_stack`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  simp[] >> pairarg_tac >> gvs[] >>
  `ALL_DISTINCT (FILTER P (stack_pop 1 qs.ps_stack)) /\
   (!op. MEM op (stack_pop 1 qs.ps_stack) ==> MEM op ps.ps_stack)` by
    (irule regional_perm_pop_inventory >> metis_tac[SND]) >>
  first_x_assum (qspecl_then [`acc ++ swap_ops ++ [SOPop 1]`,
    `qs with ps_stack := stack_pop 1 qs.ps_stack`] mp_tac) >>
  simp[] >> metis_tac[]
QED

Theorem regional_popmany_fold_slots_layout[local]:
  !xs acc ps.
  plan_slots_bounded sb ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  let qs = SND (FOLDL (\(ops, ps) v.
      case stack_get_depth v ps.ps_stack of
        NONE => (ops, ps)
      | SOME dist =>
          let (swap_ops, qs) =
            if dist = 0 then ([], ps) else do_swap dist ps in
          (ops ++ swap_ops ++ [SOPop 1],
           qs with ps_stack := stack_pop 1 qs.ps_stack)) (acc,ps) xs) in
  plan_slots_bounded sb qs /\
  spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  Induct >> simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  fs[LET_THM] >> Cases_on `stack_get_depth h ps.ps_stack`
  >- (simp[] >> first_x_assum irule >> simp[]) >>
  rename1 `stack_get_depth h ps.ps_stack = SOME d` >>
  drule stack_get_depth_props >> strip_tac >>
  drule_all do_swap_layout_wf >> strip_tac >>
  `plan_slots_bounded sb (SND (do_swap d ps))` by
    (irule do_swap_plan_slots_bounded >> metis_tac[PAIR]) >>
  Cases_on `d = 0`
  >- (simp[] >> first_x_assum irule >> gvs[plan_slots_bounded_def]) >>
  simp[] >> pairarg_tac >> gvs[] >> first_x_assum irule >>
  gvs[plan_slots_bounded_def]
QED

Theorem regional_popmany_marked_inventory:
  ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack) ==>
  ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker)
    (SND (popmany_plan vs ps)).ps_stack) /\
  (!op. MEM op (SND (popmany_plan vs ps)).ps_stack ==> MEM op ps.ps_stack)
Proof
  strip_tac >> Cases_on `vs` >- simp[popmany_plan_def] >>
  simp[popmany_plan_def, LET_THM] >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (`LENGTH (h::t) < LENGTH ps.ps_stack` by
            (irule contiguous_top_stack_bound >> simp[]) >>
          drule do_swap_stack_perm >> strip_tac >>
          pairarg_tac >> gvs[] >>
          irule regional_perm_pop_inventory >> metis_tac[SND]) >>
      simp[popmany_individual_def, LET_THM] >>
      irule (SRULE[LET_THM] regional_popmany_fold_marked_inventory) >> simp[]) >>
  simp[popmany_individual_def, LET_THM] >>
  irule (SRULE[LET_THM] regional_popmany_fold_marked_inventory) >> simp[]
QED

Theorem regional_popmany_slots_layout:
  plan_slots_bounded sb ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  plan_slots_bounded sb (SND (popmany_plan vs ps)) /\
  spill_alloc_layout_wf (SND (popmany_plan vs ps)).ps_alloc
    (SND (popmany_plan vs ps)).ps_spilled
Proof
  strip_tac >> Cases_on `vs` >- simp[popmany_plan_def] >>
  simp[popmany_plan_def, LET_THM] >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (`plan_slots_bounded sb (SND (do_swap (LENGTH (h::t)) ps))` by
            (irule do_swap_plan_slots_bounded >> metis_tac[PAIR]) >>
          `LENGTH (h::t) < LENGTH ps.ps_stack` by
            (irule contiguous_top_stack_bound >> simp[]) >>
          drule_all do_swap_layout_wf >> strip_tac >>
          pairarg_tac >> gvs[plan_slots_bounded_def] >> metis_tac[]) >>
      simp[popmany_individual_def, LET_THM] >>
      irule (SRULE[LET_THM] regional_popmany_fold_slots_layout) >> simp[]) >>
  simp[popmany_individual_def, LET_THM] >>
  irule (SRULE[LET_THM] regional_popmany_fold_slots_layout) >> simp[]
QED

Theorem regional_optimistic_slots_layout:
  plan_slots_bounded sb ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  plan_slots_bounded sb (SND (optimistic_swap_plan dfg inst nl next_term ps)) /\
  spill_alloc_layout_wf (SND (optimistic_swap_plan dfg inst nl next_term ps)).ps_alloc
    (SND (optimistic_swap_plan dfg inst nl next_term ps)).ps_spilled
Proof
  strip_tac >> simp[optimistic_swap_plan_def] >>
  Cases_on `next_term` >- simp[] >>
  Cases_on `inst.inst_outputs = []` >- simp[] >>
  Cases_on `nl = []` >- simp[] >>
  Cases_on `operand_equiv dfg (Var (LAST inst.inst_outputs)) (Var (LAST nl))`
  >- simp[] >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >- simp[] >>
  rename1 `stack_get_depth _ _ = SOME d` >> simp[] >>
  drule stack_get_depth_props >> strip_tac >>
  drule_all do_swap_layout_wf >> strip_tac >> simp[] >>
  irule do_swap_plan_slots_bounded >> metis_tac[PAIR]
QED

Theorem regional_clean_stack_slots_layout:
  clean_stack_plan lv cfg fn bb ps = (ops,qs) /\
  plan_slots_bounded sb ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  plan_slots_bounded sb qs /\ spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  strip_tac >> qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def, LET_THM] >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `_ = pred::rest` >> Cases_on `rest` >> simp[]
  >- (IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[]) >>
      Cases_on `lookup_block pred fn.fn_blocks` >> simp[]
      >- (strip_tac >> gvs[]) >>
      IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[plan_slots_bounded_def] >> metis_tac[]) >>
      IF_CASES_TAC >> simp[]
      >- (qmatch_goalsub_abbrev_tac `popmany_plan victims ps` >>
          pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
          drule_all regional_popmany_slots_layout >>
          disch_then (qspec_then `victims` mp_tac) >>
          simp[plan_slots_bounded_def] >> metis_tac[]) >>
      qmatch_goalsub_abbrev_tac `popmany_plan victims ps` >>
      strip_tac >> drule_all regional_popmany_slots_layout >>
      disch_then (qspec_then `victims` mp_tac) >> simp[]) >>
  rename1 `rest = more::tail` >>
  Cases_on `tail` >> simp[] >> strip_tac >> gvs[]
QED

Theorem regional_clean_stack_spilled:
  clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
  qs.ps_spilled = ps.ps_spilled
Proof
  strip_tac >> qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def, LET_THM] >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[] >>
  rename1 `_ = pred::rest` >> Cases_on `rest` >> simp[]
  >- (IF_CASES_TAC >> simp[] >>
      Cases_on `lookup_block pred fn.fn_blocks` >> simp[] >>
      IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[]) >>
      IF_CASES_TAC >> simp[]
      >- (pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
          metis_tac[rf_popmany_spilled, SND]) >>
      strip_tac >> metis_tac[rf_popmany_spilled, SND]) >>
  rename1 `rest = more::tail` >>
  Cases_on `tail` >> simp[]
QED

Theorem regional_mark_dead_filter[local]:
  FILTER (\op. op <> dead_stack_marker) (mark_dead_stack retained stk) =
  FILTER (\op. op <> dead_stack_marker /\ ~MEM op retained) stk
Proof
  Induct_on `stk` >> simp[mark_dead_stack_def] >> gen_tac >>
  fs[mark_dead_stack_def] >> Cases_on `MEM h retained` >> simp[]
QED

Theorem regional_mark_stack_wf[local]:
  generated_plan_state_wf_marked sb ps ==>
  generated_plan_state_wf_marked sb
    (ps with <|ps_stack := mark_dead_stack retained ps.ps_stack;
               ps_cleanup_promised := promised|>)
Proof
  simp[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
  strip_tac >> simp[regional_mark_dead_filter] >> conj_tac
  >- metis_tac[] >> conj_tac
  >- (`FILTER (\op. op <> dead_stack_marker /\ ~MEM op retained) ps.ps_stack =
       FILTER (\op. ~MEM op retained)
         (FILTER (\op. op <> dead_stack_marker) ps.ps_stack)` by
        simp[FILTER_FILTER, CONJ_COMM] >>
      simp[FILTER_ALL_DISTINCT] >> metis_tac[]) >>
  gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION, mark_dead_stack_def, MEM_MAP] >> metis_tac[]
QED

Theorem regional_popmany_marked_wf[local]:
  generated_plan_state_wf_marked sb ps ==>
  generated_plan_state_wf_marked sb (SND (popmany_plan vs ps))
Proof
  strip_tac >>
  `plan_slots_bounded sb ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
   ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack)` by
    gvs[generated_plan_state_wf_marked_def] >>
  drule_all regional_popmany_slots_layout >>
  disch_then (qspec_then `vs` strip_assume_tac) >>
  drule regional_popmany_marked_inventory >>
  disch_then (qspec_then `vs` strip_assume_tac) >>
  gvs[generated_plan_state_wf_marked_def, rf_popmany_spilled,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem regional_clean_stack_marked_wf:
  clean_stack_plan lv cfg fn bb ps = (ops,qs) /\
  generated_plan_state_wf_marked sb ps ==>
  generated_plan_state_wf_marked sb qs
Proof
  strip_tac >> qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def, LET_THM] >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `_ = pred::rest` >> Cases_on `rest` >> simp[]
  >- (IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[]) >>
      Cases_on `lookup_block pred fn.fn_blocks` >> simp[]
      >- (strip_tac >> gvs[]) >>
      IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[] >>
          gvs[generated_plan_state_wf_marked_def, plan_slots_bounded_def,
              FILTER_MAP, combinTheory.o_DEF, combinTheory.K_DEF,
              FILTER_EQ_NIL, pred_setTheory.DISJOINT_DEF,
              pred_setTheory.EXTENSION, MEM_MAP] >> metis_tac[]) >>
      IF_CASES_TAC >> simp[]
      >- (qmatch_goalsub_abbrev_tac `popmany_plan victims ps` >>
          pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
          irule regional_mark_stack_wf >>
          drule regional_popmany_marked_wf >>
          disch_then (qspec_then `victims` mp_tac) >> simp[]) >>
      strip_tac >>
      drule regional_popmany_marked_wf >> metis_tac[SND]) >>
  rename1 `rest = more::tail` >> Cases_on `tail` >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem regional_swap_pop_survives[local]:
  stack_get_depth v ps.ps_stack = SOME d /\
  MEM op ps.ps_stack /\ op <> v ==>
  MEM op (stack_pop 1 (SND (do_swap d ps)).ps_stack)
Proof
  strip_tac >> drule stack_get_depth_props >> strip_tac >>
  drule do_swap_stack_perm >> strip_tac >>
  `MEM op (SND (do_swap d ps)).ps_stack` by
    metis_tac[sortingTheory.PERM_MEM_EQ] >>
  `stack_peek 0 (SND (do_swap d ps)).ps_stack = v` by
    (simp[do_swap_stack_result] >> metis_tac[inventory_swap_top]) >>
  Cases_on `(SND (do_swap d ps)).ps_stack` using SNOC_CASES >>
  gvs[stack_peek_def, stack_pop_def, MEM_SNOC, TAKE_SNOC, EL_LENGTH_SNOC]
QED

Theorem regional_pop_fold_survives[local]:
  !items ops ps op.
  MEM op ps.ps_stack /\ ~MEM op items ==>
  MEM op (SND (FOLDL (\(ops,ps) v.
    case stack_get_depth v ps.ps_stack of
      NONE => (ops,ps)
    | SOME dist =>
        let (swap_ops,ps') =
          if dist = 0 then ([],ps) else do_swap dist ps in
        (ops ++ swap_ops ++ [SOPop 1],
         ps' with ps_stack := stack_pop 1 ps'.ps_stack))
    (ops,ps) items)).ps_stack
Proof
  Induct >> simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  RULE_ASSUM_TAC (REWRITE_RULE [LET_THM]) >>
  Cases_on `stack_get_depth h ps.ps_stack`
  >- (simp[] >> first_x_assum irule >> simp[]) >>
  rename1 `stack_get_depth h ps.ps_stack = SOME dist` >>
  drule_all regional_swap_pop_survives >> strip_tac >>
  Cases_on `dist = 0`
  >- (gvs[do_swap_def] >> first_x_assum irule >> simp[]) >>
  Cases_on `do_swap dist ps` >>
  rename1 `do_swap dist ps = (swap_ops,next)` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

Theorem regional_popmany_individual_survives[local]:
  MEM op ps.ps_stack /\ ~MEM op items ==>
  MEM op (SND (popmany_individual items ps)).ps_stack
Proof
  strip_tac >> simp[popmany_individual_def, LET_THM] >>
  irule (SRULE[LET_THM] regional_pop_fold_survives) >> simp[] >>
  metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ]
QED

Theorem regional_contiguous_survives[local]:
  items <> [] /\
  EVERY IS_SOME (MAP (\v. stack_get_depth v stk) items) /\
  is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v stk) items)) /\
  MEM op stk /\ ~MEM op items ==>
  MEM op (stack_pop (LENGTH items) (stack_swap (LENGTH items) (stk : operand list)))
Proof
  strip_tac >> drule_all contiguous_top_stack_bound >> strip_tac >>
  `0 < LENGTH items` by (Cases_on `items` >> gvs[]) >>
  qspecl_then [`LENGTH items`, `stk`] mp_tac inventory_bulk_split >>
  simp[] >> strip_tac >>
  drule_all inventory_contiguous_depths >> strip_tac >>
  `!x. MEM x items <=> MEM x (a::mid)` by
    (gen_tac >> drule inventory_depth_image >>
     disch_then (qspec_then `x` mp_tac) >> simp[] >>
     qspecl_then [`stem`, `a::mid`, `b`, `x`] mp_tac inventory_suffix_depths >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[arithmeticTheory.ADD1] >> metis_tac[]) >>
  gvs[inventory_bulk_result, MEM_APPEND] >> metis_tac[]
QED

Theorem regional_popmany_marked_survives:
  ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack) /\
  op <> dead_stack_marker /\ MEM op ps.ps_stack /\ ~MEM op victims ==>
  MEM op (SND (popmany_plan victims ps)).ps_stack
Proof
  strip_tac >> Cases_on `victims` >- simp[popmany_plan_def] >>
  simp[popmany_plan_def, LET_THM] >>
  IF_CASES_TAC
  >- (IF_CASES_TAC
      >- (`LENGTH (h::t) < LENGTH ps.ps_stack` by
            (irule contiguous_top_stack_bound >> simp[] >> metis_tac[]) >>
          `MEM op (stack_pop (LENGTH (h::t))
             (stack_swap (LENGTH (h::t)) ps.ps_stack))` by
            (irule regional_contiguous_survives >> simp[]) >>
          pairarg_tac >> gvs[] >>
          qspecl_then [`SUC (LENGTH t)`, `ps`] mp_tac do_swap_stack_result >>
          simp[] >> metis_tac[]) >>
      irule regional_popmany_individual_survives >> simp[]) >>
  irule regional_popmany_individual_survives >> simp[]
QED

Theorem regional_nonphi_input_boundary:
  !pred instrs live v.
    MEM v live /\
    ~MEM (Var v) (FLAT (MAP (\phi. phi.inst_operands) (collect_phis instrs))) ==>
    MEM v (input_vars_from pred instrs live)
Proof
  rpt strip_tac >> irule input_vars_from_non_phi >> simp[] >>
  rpt strip_tac >> gvs[MEM_MAP] >>
  drule cfgNormSupplyProofsTheory.MEM_phi_pairs_SND_operand_vars_pair >>
  strip_tac >>
  gvs[passSharedDefsTheory.MEM_operand_vars_eq_Var, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Theorem regional_clean_stack_protected_ownership:
  generated_plan_state_wf_marked sb ps /\
  clean_stack_plan lv cfg fn bb ps = (ops,qs) /\
  (!pred. cfg_preds_of cfg bb.bb_label = [pred] ==>
    MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at lv bb.bb_label 0))) /\
  (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
  MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> disch_tac >>
  `qs.ps_spilled = ps.ps_spilled` by metis_tac[regional_clean_stack_spilled] >>
  Cases_on `Var v IN FDOM ps.ps_spilled` >- simp[] >>
  fs[] >>
  `MEM (Var v) ps.ps_stack` by metis_tac[] >>
  `ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack)` by
    gvs[generated_plan_state_wf_marked_def] >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def, LET_THM] >>
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- (simp[] >> strip_tac >> gvs[]) >>
  rename1 `_ = pred::rest` >> Cases_on `rest` >> simp[]
  >- (IF_CASES_TAC >- (simp[] >> strip_tac >> gvs[]) >>
      Cases_on `lookup_block pred fn.fn_blocks`
      >- (simp[] >> strip_tac >> gvs[]) >> simp[] >>
      `MEM v (input_vars_from pred bb.bb_instructions
         (live_vars_at lv bb.bb_label 0))` by metis_tac[] >>
      `input_vars_from pred bb.bb_instructions
         (live_vars_at lv bb.bb_label 0) <> []` by
        (strip_tac >> gvs[]) >>
      simp[NULL_EQ] >>
      IF_CASES_TAC
      >- (qmatch_goalsub_abbrev_tac `popmany_plan victims ps` >>
          `~MEM (Var v) victims` by
            (simp[Abbr `victims`, MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
          `MEM (Var v) (SND (popmany_plan victims ps)).ps_stack` by
            (irule regional_popmany_marked_survives >>
             simp[dead_stack_marker_def]) >>
          pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
          simp[mark_dead_stack_def, MEM_MAP] >>
          qexists_tac `Var v` >> simp[] >>
          simp[MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
      strip_tac >>
      qmatch_asmsub_abbrev_tac `popmany_plan victims ps` >>
      `MEM (Var v) (SND (popmany_plan victims ps)).ps_stack` by
        (irule regional_popmany_marked_survives >>
         simp[dead_stack_marker_def, Abbr `victims`, MEM_MAP, MEM_FILTER] >>
         metis_tac[]) >> gvs[]) >>
  rename1 `rest = more::tail` >> Cases_on `tail` >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem regional_clean_stack_nonmarker_origin:
  generated_plan_state_wf_marked sb ps /\
  clean_stack_plan lv cfg fn bb ps = (ops,qs) /\
  MEM op qs.ps_stack /\ op <> dead_stack_marker ==>
  MEM op ps.ps_stack
Proof
  strip_tac >>
  `ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack)` by
    gvs[generated_plan_state_wf_marked_def] >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def, LET_THM] >>
  Cases_on `cfg_preds_of cfg bb.bb_label` >> simp[] >>
  rename1 `_ = pred::rest` >> Cases_on `rest` >> simp[]
  >- (IF_CASES_TAC >> simp[] >>
      Cases_on `lookup_block pred fn.fn_blocks` >> simp[] >>
      IF_CASES_TAC >> simp[]
      >- (strip_tac >> gvs[MEM_MAP, combinTheory.K_DEF]) >>
      IF_CASES_TAC >> simp[]
      >- (qmatch_goalsub_abbrev_tac `popmany_plan victims ps` >>
          pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
          drule regional_popmany_marked_inventory >>
          disch_then (qspec_then `victims` mp_tac) >>
          gvs[mark_dead_stack_def, MEM_MAP] >> metis_tac[]) >>
      strip_tac >> drule regional_popmany_marked_inventory >>
      metis_tac[SND]) >>
  rename1 `rest = more::tail` >> Cases_on `tail` >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem regional_clean_stack_identity_predicate:
  generated_plan_state_wf_marked sb ps /\
  clean_stack_plan lv cfg fn bb ps = (ops,qs) /\
  P dead_stack_marker /\
  (!op. MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled ==> P op) ==>
  (!op. MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled ==> P op)
Proof
  strip_tac >> drule regional_clean_stack_spilled >> strip_tac >>
  rpt strip_tac >> Cases_on `op = dead_stack_marker` >> gvs[] >>
  metis_tac[regional_clean_stack_nonmarker_origin]
QED

Theorem regional_prepare_params_slots_layout:
  prepare_params_plan lv fn ps = (ops,qs) /\
  plan_slots_bounded sb ps /\
  spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled ==>
  plan_slots_bounded sb qs /\ spill_alloc_layout_wf qs.ps_alloc qs.ps_spilled
Proof
  strip_tac >> qpat_x_assum `prepare_params_plan _ _ _ = _` mp_tac >>
  simp[prepare_params_plan_def, LET_THM, parameter_stack_fold] >>
  IF_CASES_TAC >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `popmany_plan victims installed` >>
  `plan_slots_bounded sb installed /\
   spill_alloc_layout_wf installed.ps_alloc installed.ps_spilled` by
    simp[Abbr `installed`, plan_slots_bounded_def] >>
  drule_all regional_popmany_slots_layout >>
  disch_then (qspec_then `victims` mp_tac) >> simp[] >> strip_tac >>
  drule_all regional_optimistic_slots_layout >> metis_tac[SND]
QED

Theorem regional_prepare_params_initial_wf:
  codegen_ready_fn fn /\
  prepare_params_plan (liveness_analyze fn) fn
    ((init_cleanup_plan_state ch growth sb ctr) with
      <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) = (ops,qs) ==>
  generated_plan_state_wf_marked sb qs
Proof
  strip_tac >>
  drule_all regional_prepare_params_initial_spilled >> strip_tac >>
  drule_all regional_prepare_params_initial_distinct >> strip_tac >>
  qmatch_asmsub_abbrev_tac `prepare_params_plan _ _ initial` >>
  `plan_slots_bounded sb initial /\
   spill_alloc_layout_wf initial.ps_alloc initial.ps_spilled` by
    simp[Abbr `initial`, init_cleanup_plan_state_def, init_plan_state_def,
      init_spill_alloc_def, plan_slots_bounded_def, alloc_slots_bounded_def,
      spill_alloc_layout_wf_def] >>
  drule_all regional_prepare_params_slots_layout >> strip_tac >>
  simp[generated_plan_state_wf_marked_def, FILTER_ALL_DISTINCT]
QED

Theorem regional_param_output_normalize[local]:
  codegen_ready_fn fn /\ MEM inst (fn_insts fn) /\
  is_param_opcode inst.inst_opcode /\ MEM v inst.inst_outputs ==>
  normalize_operand (dfg_build_function fn) [] (Var v) = Var v
Proof
  strip_tac >> drule_all dfg_build_function_defs_complete >> strip_tac >>
  rename1 `dfg_get_def (dfg_build_function fn) v = SOME found` >>
  `found = inst` by
    (drule dfg_build_function_correct >> strip_tac >>
     `ssa_form fn` by gvs[codegen_ready_fn_def] >>
     metis_tac[ssa_unique_output]) >>
  gvs[dfg_get_def_def] >> simp[Once normalize_operand_def] >>
  gvs[is_param_opcode_iff]
QED

Theorem regional_param_suffix_freshness[local]:
  codegen_ready_fn fn /\
  MEM param (get_params (HD fn.fn_blocks).bb_instructions) /\
  MEM v param.inst_outputs /\
  LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <= j /\
  j < LENGTH (HD fn.fn_blocks).bb_instructions ==>
  ~MEM v (EL j (HD fn.fn_blocks).bb_instructions).inst_outputs
Proof
  strip_tac >>
  `?i. i < LENGTH (get_params (HD fn.fn_blocks).bb_instructions) /\
    EL i (get_params (HD fn.fn_blocks).bb_instructions) = param` by
    metis_tac[MEM_EL] >>
  qspec_then `(HD fn.fn_blocks).bb_instructions` strip_assume_tac get_params_suffix >>
  `i < LENGTH (HD fn.fn_blocks).bb_instructions /\ i <> j /\
   EL i (HD fn.fn_blocks).bb_instructions = param` by
    (rpt conj_tac
     >- (`LENGTH (HD fn.fn_blocks).bb_instructions =
           LENGTH (get_params (HD fn.fn_blocks).bb_instructions) + LENGTH suffix`
           by metis_tac[LENGTH_APPEND] >> decide_tac)
     >- decide_tac >>
     qpat_x_assum `_ = _ ++ _` (fn th => once_rewrite_tac[th]) >>
     simp[EL_APPEND_EQN]) >>
  `MEM (HD fn.fn_blocks) fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[codegen_ready_fn_def, wf_function_def, fn_has_entry_def]) >>
  metis_tac[ready_output_other_location]
QED

Theorem regional_param_member_shape[local]:
  param_insts_from n insts /\ MEM inst insts ==>
  is_param_opcode inst.inst_opcode /\ LENGTH inst.inst_outputs = 1
Proof
  strip_tac >>
  qpat_x_assum `MEM inst insts`
    (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  gvs[param_insts_from_append, param_insts_from_def, param_inst_at_def]
QED

Theorem regional_prepare_params_initial_freshness:
  codegen_ready_fn fn /\
  prepare_params_plan (liveness_analyze fn) fn
    ((init_cleanup_plan_state ch growth sb ctr) with
      <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) = (ops,qs) ==>
  !j op v.
    LENGTH (get_params (HD fn.fn_blocks).bb_instructions) <= j /\
    j < LENGTH (HD fn.fn_blocks).bb_instructions /\
    (MEM op qs.ps_stack \/ op IN FDOM qs.ps_spilled) /\
    (op = Var v \/ normalize_operand (dfg_build_function fn) [] op = Var v) ==>
    ~MEM v (EL j (HD fn.fn_blocks).bb_instructions).inst_outputs
Proof
  strip_tac >>
  drule_all regional_prepare_params_initial_spilled >> strip_tac >>
  drule_all regional_prepare_params_initial_membership >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `MEM op (MAP (\i. Var (HD i.inst_outputs))
    (get_params (HD fn.fn_blocks).bb_instructions))` by gvs[] >>
  fs[MEM_MAP] >> rename1 `MEM param (get_params _)` >>
  `param_insts_from 0 (get_params (HD fn.fn_blocks).bb_instructions)` by
    metis_tac[canonical_get_params_layout] >>
  `is_param_opcode param.inst_opcode /\ LENGTH param.inst_outputs = 1` by
    metis_tac[regional_param_member_shape] >>
  `MEM (HD param.inst_outputs) param.inst_outputs` by
    (Cases_on `param.inst_outputs` >> gvs[]) >>
  `MEM param (fn_insts fn)` by
    (qspec_then `(HD fn.fn_blocks).bb_instructions` strip_assume_tac get_params_suffix >>
     `MEM param (HD fn.fn_blocks).bb_instructions` by metis_tac[MEM_APPEND] >>
     `fn.fn_blocks <> []` by
       gvs[codegen_ready_fn_def, wf_function_def, fn_has_entry_def] >>
     simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     Cases_on `fn.fn_blocks` >> gvs[] >> metis_tac[]) >>
  drule_all regional_param_output_normalize >> strip_tac >> gvs[] >>
  metis_tac[regional_param_suffix_freshness]
QED

Theorem regional_nonentry_initial_wf:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
    sb ctr = SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth sb ctr) lbl ps_l /\
  bb <> HD fn.fn_blocks /\
  start = ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|> /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
     clean_stack_plan liveness cfg fn bb start else ([],start)) = (clean_ops,ps2) ==>
  generated_plan_state_wf_marked sb ps2
Proof
  strip_tac >> drule_all lineage_state_static >> strip_tac >>
  `generated_plan_state_wf_marked sb start` by
    (gvs[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
     metis_tac[]) >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1` >> gvs[] >>
  metis_tac[regional_clean_stack_marked_wf]
QED


Theorem regional_nonentry_initial_coverage:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
    sb ctr = SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth sb ctr) lbl ps_l /\
  bb <> HD fn.fn_blocks /\
  start = ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|> /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
     clean_stack_plan liveness cfg fn bb start else ([],start)) = (clean_ops,ps2) ==>
  !v. MEM v (live_vars_at liveness lbl 0) /\
    ~MEM (Var v) (FLAT (MAP (\inst. inst.inst_operands)
       (collect_phis bb.bb_instructions))) ==>
    MEM (Var v) ps2.ps_stack \/ Var v IN FDOM ps2.ps_spilled
Proof
  strip_tac >> drule_all lineage_state_static >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `generated_plan_state_wf_marked sb start` by
    (gvs[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
     metis_tac[]) >>
  rpt strip_tac >>
  `MEM (Var v) start.ps_stack \/ Var v IN FDOM start.ps_spilled` by
    (simp[] >> metis_tac[]) >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1` >> gvs[] >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _`
    (mp_then (Pos (el 2)) mp_tac regional_clean_stack_protected_ownership) >>
  disch_then (qspec_then `v` mp_tac) >>
  simp[] >>
  `!pred. MEM v (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) bb.bb_label 0))` by
    (gen_tac >> irule regional_nonphi_input_boundary >> simp[]) >>
  metis_tac[]
QED

Theorem regional_nonentry_initial_freshness:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
    sb ctr = SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth sb ctr) lbl ps_l /\
  bb <> HD fn.fn_blocks /\
  start = ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|> /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
     clean_stack_plan liveness cfg fn bb start else ([],start)) = (clean_ops,ps2) ==>
  !op v. (MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled) /\
    ~MEM op (FLAT (MAP (\inst. inst.inst_operands)
      (collect_phis bb.bb_instructions))) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  strip_tac >> drule_all lineage_state_static >> strip_tac >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1` >> gvs[]
  >- (`generated_plan_state_wf_marked sb
         (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)` by
        (gvs[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
         metis_tac[]) >>
      rpt strip_tac >>
      `op <> dead_stack_marker` by
        (strip_tac >> gvs[dead_stack_marker_def, normalize_operand_def]) >>
      `ps2.ps_spilled = ps_l.ps_spilled` by
        (drule regional_clean_stack_spilled >> simp[]) >>
      `!x. MEM x ps2.ps_stack /\ x <> dead_stack_marker ==>
            MEM x ps_l.ps_stack` by
        (rpt strip_tac >> drule_all regional_clean_stack_nonmarker_origin >> simp[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem regional_nonentry_initial_single_freshness:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
    sb ctr = SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth sb ctr) lbl ps_l /\
  bb <> HD fn.fn_blocks /\
  start = ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|> /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
     clean_stack_plan liveness cfg fn bb start else ([],start)) = (clean_ops,ps2) ==>
  LENGTH (cfg_preds_of cfg lbl) <= 1 ==>
  !op v. (MEM op ps2.ps_stack \/ op IN FDOM ps2.ps_spilled) /\
    (op = Var v \/ normalize_operand dfg [] op = Var v) ==>
    ~MEM v (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  strip_tac >> drule_all lineage_state_static >> strip_tac >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1` >> gvs[]
  >- (`generated_plan_state_wf_marked sb
         (ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>)` by
        (gvs[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
         metis_tac[]) >>
      rpt strip_tac >>
      `op <> dead_stack_marker` by
        (strip_tac >> gvs[dead_stack_marker_def, normalize_operand_def]) >>
      `ps2.ps_spilled = ps_l.ps_spilled` by
        (drule regional_clean_stack_spilled >> simp[]) >>
      `!x. MEM x ps2.ps_stack /\ x <> dead_stack_marker ==>
            MEM x ps_l.ps_stack` by
        (rpt strip_tac >> drule_all regional_clean_stack_nonmarker_origin >> simp[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Theorem regional_nonentry_initial_phi_ownership:
  liveness = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed liveness dfg cfg ch growth fn
    sb ctr = SOME (fn_ops,ps_end) /\
  EVERY (\bb'. EVERY (\inst. EVERY (\op. op <> dead_stack_marker)
    inst.inst_operands) bb'.bb_instructions) fn.fn_blocks /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lineage_state liveness dfg cfg fn
    (init_cleanup_plan_state ch growth sb ctr) lbl ps_l /\
  bb <> HD fn.fn_blocks /\
  start = ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|> /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
     clean_stack_plan liveness cfg fn bb start else ([],start)) = (clean_ops,ps2) ==>
  EVERY (\phi. ?!v. MEM (Var v) phi.inst_operands /\
    (MEM (Var v) ps2.ps_stack \/ Var v IN FDOM ps2.ps_spilled))
    (collect_phis bb.bb_instructions)
Proof
  strip_tac >> drule_all lineage_state_static >> strip_tac >>
  Cases_on `collect_phis bb.bb_instructions = []` >- simp[] >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  gvs[] >>
  drule_all regional_phi_preparation_identity >>
  disch_then (qspecl_then [`liveness_analyze fn`,
    `ps_l with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>`] mp_tac) >>
  simp[] >> strip_tac >> gvs[]
QED

(* Both cuts retain the original tail, hence the same lookahead. *)
Theorem regional_block_prefix_cut:
  !a insts lv dfg cfg fn lbl halt np bl i b ps ops qs.
    a <= LENGTH insts ==>
    (generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i (a+b)
       insts ps = SOME (ops,qs) <=>
     ?pre mid post.
       generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i a
         insts ps = SOME (pre,mid) /\
       generate_block_insts_prefix lv dfg cfg fn lbl halt np bl (i+a) b
         (DROP a insts) mid = SOME (post,qs) /\
       ops = pre ++ post)
Proof
  Induct_on `a`
  >- simp[generate_block_insts_prefix_def] >>
  gen_tac >> Cases_on `insts` >- simp[] >>
  first_x_assum (qspec_then `t` mp_tac) >>
  disch_tac >> rpt gen_tac >> disch_tac >>
  fs[LENGTH] >>
  pure_rewrite_tac[arithmeticTheory.ADD_CLAUSES] >>
  simp[generate_block_insts_prefix_def, LET_THM, AllCaseEqs(), PULL_EXISTS] >>
  simp[arithmeticTheory.ADD1] >>
  eq_tac >> strip_tac >> gvs[arithmeticTheory.ADD1] >>
  rpt (first_assum $ irule_at Any) >> simp[arithmeticTheory.ADD1]
QED

Theorem regional_regular_core_marked_wf:
  generated_plan_state_wf_marked sb ps /\
  LENGTH operands <= 16 /\ PERM pending operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,mid) /\
  reorder_plan dfg pending mid = (rops,arranged) ==>
  generated_plan_state_wf_marked sb
    (arranged with ps_stack := stack_pop (LENGTH operands) arranged.ps_stack)
Proof
  strip_tac >>
  `residual_budget_wf_marked sb [] ps` by
    (drule generated_plan_state_wf_marked_residual_nil >> simp[]) >>
  `residual_budget_wf_marked sb operands mid` by
    (drule_all emit_input_plan_residual_budget_wf_marked >> simp[]) >>
  `residual_budget_wf_marked sb pending mid` by
    metis_tac[residual_budget_wf_marked_perm] >>
  `LENGTH pending = LENGTH operands` by metis_tac[PERM_LENGTH] >>
  `LENGTH operands <= LENGTH mid.ps_stack` by
    (drule_all available_input_plan_length >> simp[]) >>
  `!x. LIST_ELEM_COUNT x pending <= LIST_ELEM_COUNT x mid.ps_stack` by
    (drule_all emit_input_plan_stack_counts >>
     drule perm_operand_counts >> simp[]) >>
  `LENGTH pending <= LENGTH mid.ps_stack /\ LENGTH pending <= 16` by simp[] >>
  `plan_state_residual_wf_marked sb pending (LENGTH pending) arranged` by
    (drule_all reorder_plan_materialised_arranged_marked >> simp[]) >>
  drule plan_state_residual_wf_marked_pop >>
  simp[generated_plan_state_wf_marked_def]
QED

Theorem regional_release_fold_stack[local]:
  !xs ps stk.
    FOLDL (\qs (op,off). qs with
      <|ps_spilled := qs.ps_spilled \\ op;
        ps_alloc := free_spill_slot off qs.ps_alloc|>)
      (ps with ps_stack := stk) xs =
    (FOLDL (\qs (op,off). qs with
      <|ps_spilled := qs.ps_spilled \\ op;
        ps_alloc := free_spill_slot off qs.ps_alloc|>) ps xs)
      with ps_stack := stk
Proof
  Induct >> simp[] >> gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[]
QED

Theorem regional_release_stack_update[local]:
  release_dead_spills nl (ps with ps_stack := stk) =
  (release_dead_spills nl ps) with ps_stack := stk
Proof
  simp[release_dead_spills_def, regional_release_fold_stack]
QED

Theorem regional_release_marked_wf[local]:
  generated_plan_state_wf_marked sb ps ==>
  generated_plan_state_wf_marked sb (release_dead_spills nl ps)
Proof
  strip_tac >>
  `generated_plan_state_wf sb
    (ps with ps_stack := FILTER (\op. op <> dead_stack_marker) ps.ps_stack)` by
    (gvs[generated_plan_state_wf_def, generated_plan_state_wf_marked_def,
         plan_slots_bounded_def, pred_setTheory.DISJOINT_DEF,
         pred_setTheory.EXTENSION, MEM_FILTER] >> metis_tac[]) >>
  drule generated_plan_state_wf_release_dead_spills >>
  disch_then (qspec_then `nl` mp_tac) >>
  simp[regional_release_stack_update, generated_plan_state_wf_def,
       plan_slots_bounded_def] >> strip_tac >>
  gvs[generated_plan_state_wf_marked_def, plan_slots_bounded_def,
      release_dead_spills_stack, pred_setTheory.DISJOINT_DEF,
      pred_setTheory.EXTENSION] >>
  `!x. x IN FDOM (release_dead_spills nl ps).ps_spilled ==>
       x IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     `?off. FLOOKUP (release_dead_spills nl ps).ps_spilled x = SOME off` by
       simp[finite_mapTheory.FLOOKUP_DEF] >>
     drule rf_release_spill_lookup >> simp[finite_mapTheory.FLOOKUP_DEF]) >>
  metis_tac[]
QED

Theorem regional_optimistic_marked_wf[local]:
  generated_plan_state_wf_marked sb ps ==>
  generated_plan_state_wf_marked sb
    (SND (optimistic_swap_plan dfg inst nl next_term ps))
Proof
  strip_tac >> simp[optimistic_swap_plan_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  Cases_on `stack_get_depth (Var (LAST nl)) ps.ps_stack` >> simp[] >>
  rename1 `stack_get_depth _ _ = SOME dist` >>
  drule stack_get_depth_props >> strip_tac >>
  `plan_slots_bounded sb ps /\
   spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
    gvs[generated_plan_state_wf_marked_def] >>
  drule_all do_swap_layout_wf >> strip_tac >>
  `plan_slots_bounded sb (SND (do_swap dist ps))` by
    (irule do_swap_plan_slots_bounded >> metis_tac[PAIR]) >>
  `PERM (SND (do_swap dist ps)).ps_stack ps.ps_stack` by
    metis_tac[do_swap_stack_perm] >>
  gvs[generated_plan_state_wf_marked_def,
      reorderSimTheory.do_swap_spilled_unchanged] >>
  conj_tac >- metis_tac[PERM_FILTER, ALL_DISTINCT_PERM] >>
  gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[PERM_MEM_EQ]
QED

Theorem regional_emit_marked_wf[local]:
  generate_emit_ops inst topics ps = (ops,qs) /\
  generated_plan_state_wf_marked sb ps ==>
  generated_plan_state_wf_marked sb qs
Proof
  strip_tac >>
  `qs.ps_stack = ps.ps_stack /\ qs.ps_spilled = ps.ps_spilled` by
    metis_tac[fnBlockPlanStaticBalanceTheory.generate_emit_ops_stack,
              inventory_emit_ops_spilled, SND] >>
  drule allocMonoTheory.generate_emit_ops_alloc >> strip_tac >>
  gvs[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
  metis_tac[]
QED

Theorem regional_push_marked_wf[local]:
  generated_plan_state_wf_marked sb ps /\
  ~MEM op ps.ps_stack /\ op NOTIN FDOM ps.ps_spilled ==>
  generated_plan_state_wf_marked sb
    (ps with ps_stack := stack_push op ps.ps_stack)
Proof
  strip_tac >>
  `plan_slots_bounded sb (ps with ps_stack := stack_push op ps.ps_stack)` by
    (gvs[generated_plan_state_wf_marked_def, plan_slots_bounded_def] >>
     metis_tac[]) >>
  gvs[generated_plan_state_wf_marked_def, stack_push_def,
      FILTER_SNOC, ALL_DISTINCT_SNOC, MEM_FILTER,
      pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  Cases_on `op = dead_stack_marker` >> gvs[]
  >- (gen_tac >> Cases_on `x = dead_stack_marker` >> gvs[]) >>
  conj_tac >- simp[ALL_DISTINCT_SNOC, MEM_FILTER] >>
  gen_tac >> Cases_on `x = op` >> gvs[]
QED

Theorem regional_outputs_marked_wf[local]:
  !outputs ps.
    generated_plan_state_wf_marked sb ps /\ ALL_DISTINCT outputs /\
    EVERY (\v. ~MEM (Var v) ps.ps_stack /\
                Var v NOTIN FDOM ps.ps_spilled) outputs ==>
    generated_plan_state_wf_marked sb
      (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
        ps outputs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  `generated_plan_state_wf_marked sb
     (ps with ps_stack := stack_push (Var h) ps.ps_stack)` by
    (irule regional_push_marked_wf >> simp[]) >>
  first_x_assum irule >> simp[] >>
  gvs[EVERY_MEM, stack_push_def] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem regional_regular_outputs_marked_wf[local]:
  generated_plan_state_wf_marked sb ps /\
  LENGTH operands <= 16 /\ PERM pending operands /\
  (!op. MEM op operands /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  emit_input_plan opc operands nl ps = (iops,mid) /\
  reorder_plan dfg pending mid = (rops,arranged) /\
  ALL_DISTINCT outputs /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled) outputs ==>
  generated_plan_state_wf_marked sb
    (FOLDL (\s out. s with ps_stack := stack_push (Var out) s.ps_stack)
      (arranged with ps_stack := stack_pop (LENGTH operands) arranged.ps_stack) outputs)
Proof
  strip_tac >>
  `generated_plan_state_wf_marked sb
    (arranged with ps_stack := stack_pop (LENGTH operands) arranged.ps_stack)` by
    (drule_all regional_regular_core_marked_wf >> simp[]) >>
  irule regional_outputs_marked_wf >> simp[] >>
  `LENGTH operands <= LENGTH mid.ps_stack` by
    (drule_all available_input_plan_length >> simp[]) >>
  `EVERY (\v. ~MEM (Var v) arranged.ps_stack /\
      Var v NOTIN FDOM arranged.ps_spilled) outputs` by
    (gvs[EVERY_MEM] >> gen_tac >> disch_tac >>
     `~MEM (Var v) mid.ps_stack /\ Var v NOTIN FDOM mid.ps_spilled` by
       metis_tac[generatedPrefixSimTheory.emit_input_plan_preserves_not_mem] >>
     `LENGTH pending = LENGTH operands` by metis_tac[PERM_LENGTH] >>
     `LENGTH pending <= LENGTH mid.ps_stack /\ LENGTH pending <= 17` by simp[] >>
     drule_all generatedPrefixSimTheory.reorder_plan_preserves_not_mem_reachable >> simp[]) >>
  gvs[EVERY_MEM, stack_pop_def] >>
  metis_tac[rich_listTheory.MEM_TAKE]
QED

Theorem regional_regular_marked_wf:
  inst.inst_opcode <> JMP /\
  generated_plan_state_wf_marked sb ps /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  ALL_DISTINCT inst.inst_outputs /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled) inst.inst_outputs /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = (ops,qs)
  ==> generated_plan_state_wf_marked sb qs
Proof
  strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `emit_input_plan _ _ _ _ = (iops,mid)` >>
  rename1 `_ = (rops,arranged)` >>
  `?pending. PERM pending (compute_operands inst) /\
    reorder_plan dfg pending mid = (rops,arranged)` by
    (irule inventory_selected_reorder >> qexists_tac `inst.inst_opcode` >>
     simp[LET_THM]) >>
  qpat_x_assum `(if _ then _ else _) = (rops,arranged)` kall_tac >> fs[] >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics pushed` >>
  `generated_plan_state_wf_marked sb pushed` by
    (simp[Abbr `pushed`] >> irule regional_regular_outputs_marked_wf >> simp[] >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >> simp[]) >>
  pairarg_tac >> simp[] >>
  rename1 `generate_emit_ops _ _ _ = (eops,emitted)` >>
  `generated_plan_state_wf_marked sb emitted` by
    (drule_all regional_emit_marked_wf >> simp[]) >>
  qpat_x_assum `Abbrev (topics = _)` kall_tac >>
  qpat_x_assum `Abbrev (pushed = _)` kall_tac >>
  Cases_on `inst.inst_outputs = []`
  >- (simp[] >> strip_tac >> gvs[] >>
      irule regional_release_marked_wf >> simp[]) >>
  simp[] >> pairarg_tac >> simp[] >>
  rename1 `_ = (pops,popped)` >>
  `generated_plan_state_wf_marked sb popped` by
    (Cases_on `~halting \/ 1 < LENGTH inst.inst_outputs` >> gvs[] >>
     metis_tac[regional_popmany_marked_wf, SND]) >>
  pairarg_tac >> simp[] >> rename1 `_ = (oopt,optimised)` >>
  `generated_plan_state_wf_marked sb optimised` by
    (Cases_on `FILTER (\out. MEM out nl) inst.inst_outputs = []` >> gvs[] >>
     metis_tac[regional_optimistic_marked_wf, SND]) >>
  strip_tac >> gvs[] >> irule regional_release_marked_wf >> simp[]
QED

Theorem regional_offset_marked_wf[local]:
  inst_wf inst /\ inst.inst_opcode = OFFSET /\
  generated_plan_state_wf_marked sb ps /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    inst.inst_outputs ==>
  generated_plan_state_wf_marked sb (SND (generate_offset_plan inst ps))
Proof
  strip_tac >> drule_all inst_wf_offset_shape >> strip_tac >>
  gvs[generate_offset_plan_def] >>
  irule regional_push_marked_wf >> simp[]
QED

Theorem regional_body_marked_wf:
  inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
  generated_plan_state_wf_marked sb ps /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  ALL_DISTINCT inst.inst_outputs /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    inst.inst_outputs /\
  generate_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = SOME (ops,qs)
  ==> generated_plan_state_wf_marked sb qs
Proof
  strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def] >>
  Cases_on `is_pre_codegen_opcode inst.inst_opcode` >> simp[] >>
  Cases_on `inst.inst_opcode = INVOKE /\ ~invoke_operands_wf inst` >> simp[] >>
  Cases_on `inst.inst_opcode = OFFSET`
  >- (strip_tac >>
      `generated_plan_state_wf_marked sb (SND (generate_offset_plan inst ps))` by
        (irule regional_offset_marked_wf >> simp[]) >> gvs[]) >>
  Cases_on `is_param_opcode inst.inst_opcode` >> simp[] >>
  Cases_on `inst.inst_opcode = NOP` >> simp[] >> strip_tac >> gvs[] >>
  irule regional_regular_marked_wf >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem regional_dead_outputs_marked_owned[local]:
  !outputs nl ps v.
  ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack) /\ MEM v nl /\
  (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==>
  MEM (Var v) (SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) outputs)) ps)).ps_stack \/
  Var v IN FDOM (SND (popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) outputs)) ps)).ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM (Var v) ps.ps_stack`
  >- (disj1_tac >> irule regional_popmany_marked_survives >>
      simp[dead_stack_marker_def, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  gvs[rf_popmany_spilled]
QED

Theorem regional_regular_marked_live_coverage:
  !inst sb ps lv dfg cfg fn nl halting next_term lbl ops qs v.
  inst.inst_opcode <> JMP /\ generated_plan_state_wf_marked sb ps /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  ALL_DISTINCT inst.inst_outputs /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    inst.inst_outputs /\
  generate_regular_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = (ops,qs) /\
  MEM v nl /\
  (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled \/ MEM v inst.inst_outputs)
  ==> MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_regular_inst_plan_def, LET_THM] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rename1 `emit_input_plan _ _ _ _ = (iops,mid)` >>
  rename1 `_ = (rops,arranged)` >>
  `?pending. PERM pending (compute_operands inst) /\
    reorder_plan dfg pending mid = (rops,arranged)` by
    (irule inventory_selected_reorder >> qexists_tac `inst.inst_opcode` >> simp[LET_THM]) >>
  qpat_x_assum `(if _ then _ else _) = (rops,arranged)` kall_tac >> fs[] >>
  `LENGTH (compute_operands inst) <= LENGTH mid.ps_stack` by
    (drule available_input_plan_length >> simp[] >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `generate_emit_ops inst topics pushed` >>
  `generated_plan_state_wf_marked sb pushed` by
    (simp[Abbr `pushed`] >> irule regional_regular_outputs_marked_wf >> simp[] >>
     goal_assum (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >> simp[]) >>
  `MEM (Var v) pushed.ps_stack \/ Var v IN FDOM pushed.ps_spilled` by
    (simp[Abbr `pushed`, inventory_output_push_stack, inventory_output_push_spilled] >>
     Cases_on `MEM v inst.inst_outputs` >- simp[MEM_MAP] >>
     `MEM (Var v) (stack_pop (LENGTH (compute_operands inst)) arranged.ps_stack) \/
      Var v IN FDOM arranged.ps_spilled` by
       (irule regional_live_ownership_residual >> metis_tac[]) >> simp[]) >>
  pairarg_tac >> simp[] >> rename1 `generate_emit_ops _ _ _ = (eops,emitted)` >>
  `generated_plan_state_wf_marked sb emitted` by
    (drule_all regional_emit_marked_wf >> simp[]) >>
  `MEM (Var v) emitted.ps_stack \/ Var v IN FDOM emitted.ps_spilled` by
    metis_tac[fnBlockPlanStaticBalanceTheory.generate_emit_ops_stack, inventory_emit_ops_spilled, SND] >>
  qpat_x_assum `Abbrev (topics = _)` kall_tac >>
  qpat_x_assum `Abbrev (pushed = _)` kall_tac >>
  (Cases_on `inst.inst_outputs = []`
  >- (simp[] >> strip_tac >> gvs[] >> metis_tac[rf_release_live_owned, release_dead_spills_stack]) >>
  `MEM (Var v) (SND (if ~halting \/ LENGTH inst.inst_outputs > 1 then
      popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) emitted
      else ([],emitted))).ps_stack \/
   Var v IN FDOM (SND (if ~halting \/ LENGTH inst.inst_outputs > 1 then
      popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs)) emitted
      else ([],emitted))).ps_spilled` by
    (IF_CASES_TAC >> simp[] >> irule regional_dead_outputs_marked_owned >>
     gvs[generated_plan_state_wf_marked_def]) >>
  simp[] >> pairarg_tac >> fs[] >> pairarg_tac >> simp[] >>
  rename1 `_ = (oopt,optimised)` >>
  `MEM (Var v) optimised.ps_stack \/ Var v IN FDOM optimised.ps_spilled` by
    (Cases_on `FILTER (\out. MEM out nl) inst.inst_outputs = []` >> gvs[] >>
     metis_tac[regional_optimistic_ownership, SND]) >>
  strip_tac >> gvs[] >> metis_tac[rf_release_live_owned, release_dead_spills_stack])
QED

Theorem regional_indexed_body_marked_live_coverage:
  !fn bb i inst sb ps dfg cfg halting next_term ops qs.
  wf_function fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  inst_wf inst /\ inst.inst_opcode <> PHI /\ inst.inst_opcode <> JMP /\
  ~is_param_opcode inst.inst_opcode /\
  generated_plan_state_wf_marked sb ps /\
  LENGTH (compute_operands inst) <= 16 /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
  ALL_DISTINCT inst.inst_outputs /\
  EVERY (\v. ~MEM (Var v) ps.ps_stack /\ Var v NOTIN FDOM ps.ps_spilled)
    inst.inst_outputs /\
  (!v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) ==>
    MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) /\
  generate_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halting next_term
    bb.bb_label ps = SOME (ops,qs) ==>
  !v. MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) ==>
    MEM (Var v) qs.ps_stack \/ Var v IN FDOM qs.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `v` >> disch_tac >>
  Cases_on `inst.inst_opcode = NOP \/ inst.inst_opcode = OFFSET`
  >- (drule_all regional_indexed_special_live_coverage >> simp[]) >>
  `generate_regular_inst_plan (liveness_analyze fn) dfg cfg fn inst
    (live_vars_at (liveness_analyze fn) bb.bb_label (SUC i)) halting next_term
    bb.bb_label ps = (ops,qs)` by
    (qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[generate_inst_plan_def, LET_THM] >> rpt IF_CASES_TAC >> gvs[]) >>
  `MEM v inst.inst_outputs \/
   MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i)` by
    (Cases_on `MEM v inst.inst_outputs` >- simp[] >>
     disj2_tac >> irule (SRULE[LET_THM, inst_defs_def] live_vars_at_propagate) >>
     metis_tac[]) >>
  irule regional_regular_marked_live_coverage >>
  goal_assum (drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
  qexists_tac `sb` >> simp[] >> metis_tac[]
QED

Theorem regional_entry_no_preds:
  codegen_ready_fn fn ==>
  cfg_preds_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label = []
Proof
  strip_tac >>
  `fn.fn_blocks <> [] /\ block_entries_ready (cfg_analyze fn) fn` by
    gvs[codegen_ready_fn_def, wf_function_def, fn_has_entry_def] >>
  Cases_on `fn.fn_blocks` >>
  gvs[block_entries_ready_def, entry_block_def, NULL_EQ]
QED

Theorem regional_entry_lineage_initial:
  codegen_ready_fn fn /\
  lineage_state lv dfg (cfg_analyze fn) fn ps0 (HD fn.fn_blocks).bb_label ps ==>
  ps = ps0
Proof
  strip_tac >>
  `cfg_preds_of (cfg_analyze fn) (HD fn.fn_blocks).bb_label = []` by
    metis_tac[regional_entry_no_preds] >>
  qpat_x_assum `lineage_state _ _ _ _ _ _ _` mp_tac >>
  simp[Once lineage_state_cases] >> strip_tac >>
  gvs[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond]
QED

Theorem regional_insts_marker_free:
  !insts i ps ops qs.
    EVERY codegen_ready_inst insts /\ EVERY inst_wf insts /\
    ~MEM dead_stack_marker ps.ps_stack /\
    generate_block_insts_plan lv dfg cfg fn lbl F np bl i insts ps =
      SOME (ops,qs) ==>
    ~MEM dead_stack_marker qs.ps_stack
Proof
  Induct >> simp[generate_block_insts_plan_def] >> rpt strip_tac >>
  gvs[generate_block_insts_plan_def, LET_THM, AllCaseEqs()] >>
  metis_tac[inventory_inst_marker_free]
QED

Theorem regional_prefix_marker_free:
  !j insts i ps ops qs.
    EVERY codegen_ready_inst insts /\ EVERY inst_wf insts /\
    ~MEM dead_stack_marker ps.ps_stack /\
    generate_block_insts_prefix lv dfg cfg fn lbl F np bl i j insts ps =
      SOME (ops,qs) ==>
    ~MEM dead_stack_marker qs.ps_stack
Proof
  Induct >- (simp[generate_block_insts_prefix_def] >> metis_tac[]) >>
  Cases_on `insts` >> simp[generate_block_insts_prefix_def] >> rpt strip_tac >>
  gvs[generate_block_insts_prefix_def, LET_THM, AllCaseEqs()] >>
  metis_tac[inventory_inst_marker_free]
QED

Theorem regional_ret_reaching_nonhalting:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  cfg_path (cfg_analyze fn) lbl target ==>
  ~bb_is_halting bb
Proof
  metis_tac[ready_halting_not_ret_reaching]
QED

Theorem regional_non_param_insts_ready:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  EVERY codegen_ready_inst (non_param_insts bb)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  gvs[codegen_ready_fn_def, non_param_insts_def, EVERY_MEM, MEM_FILTER] >>
  metis_tac[]
QED

Theorem regional_non_param_insts_wf:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
  EVERY inst_wf (non_param_insts bb)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  gvs[codegen_ready_fn_def, fn_inst_wf_def, non_param_insts_def,
      EVERY_MEM, MEM_FILTER] >> metis_tac[]
QED

Theorem regional_dfs_params_marker_free:
  codegen_ready_fn fn /\
  dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
    (init_cleanup_plan_state ch growth sb ctr) bb.bb_label ps /\
  ~MEM dead_stack_marker ps.ps_stack /\
  (if bb = HD fn.fn_blocks then
     prepare_params_plan (liveness_analyze fn) fn ps
   else ([],ps)) = (ops,qs) ==>
  ~MEM dead_stack_marker qs.ps_stack
Proof
  strip_tac >> Cases_on `bb = HD fn.fn_blocks` >-
    (gvs[] >>
     `lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
        (init_cleanup_plan_state ch growth sb ctr)
        (HD fn.fn_blocks).bb_label ps` by
       metis_tac[dfs_block_state_lineage_state] >>
     `ps = init_cleanup_plan_state ch growth sb ctr` by
       metis_tac[regional_entry_lineage_initial] >>
     gvs[] >>
     `prepare_params_plan (liveness_analyze fn) fn
        ((init_cleanup_plan_state ch growth sb ctr) with
          <|ps_cleanup_height := (init_cleanup_plan_state ch growth sb ctr).ps_cleanup_height;
            ps_cleanup_promised := (init_cleanup_plan_state ch growth sb ctr).ps_cleanup_promised|>) =
        (ops,qs)` by
       gvs[init_cleanup_plan_state_def, stackPlanTypesTheory.init_plan_state_def] >>
     drule_all regional_prepare_params_initial_membership >>
     disch_then (qspec_then `dead_stack_marker` mp_tac) >>
     simp[MEM_MAP, dead_stack_marker_def]) >>
  gvs[]
QED

Theorem regional_ret_cleanup_marker_free:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target /\
  ~ps.ps_cleanup_promised /\ ~MEM dead_stack_marker ps.ps_stack /\
  clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
  ~MEM dead_stack_marker qs.ps_stack
Proof
  strip_tac >> gvs[] >>
  `!height growth n. ~cleanup_elision_safe height growth (cfg_analyze fn) fn bb n` by
    metis_tac[ret_reaching_cleanup_not_safe] >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def, LET_THM] >>
  Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> simp[] >-
    (strip_tac >> gvs[]) >>
  rename1 `cfg_preds_of (cfg_analyze fn) bb.bb_label = pred::rest` >>
  Cases_on `rest` >> simp[] >-
    (IF_CASES_TAC >> simp[] >- (strip_tac >> gvs[]) >>
     Cases_on `lookup_block pred fn.fn_blocks` >> simp[] >-
       (strip_tac >> gvs[]) >>
     rename1 `lookup_block pred fn.fn_blocks = SOME pred_bb` >>
     strip_tac >>
     `EVERY (\op. op <> dead_stack_marker) ps.ps_stack` by
       simp[EVERY_MEM] >>
     drule inventory_popmany_every >>
     disch_then (qspec_then `MAP Var
       (FILTER (\v. ~MEM v (input_vars_from pred bb.bb_instructions
          (live_vars_at lv bb.bb_label 0)))
         (live_vars_at lv pred (LENGTH pred_bb.bb_instructions)))` mp_tac) >>
     gvs[EVERY_MEM]) >>
  strip_tac >> gvs[]
QED

Theorem regional_dfs_block_marker_free:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_path cfg lbl target /\
  dfs_block_state (liveness_analyze fn) dfg cfg fn
    (init_cleanup_plan_state ch growth sb ctr) lbl ps /\
  ~MEM dead_stack_marker ps.ps_stack /\
  generate_block_plan (liveness_analyze fn) dfg cfg fn bb ps = SOME (ops,qs) ==>
  ~MEM dead_stack_marker qs.ps_stack
Proof
  strip_tac >> gvs[] >>
  `lbl = bb.bb_label` by metis_tac[lookup_block_label] >>
  `~ps.ps_cleanup_promised` by metis_tac[ret_region_dfs_block_unpromised] >>
  `~bb_is_halting bb` by metis_tac[regional_ret_reaching_nonhalting] >>
  `EVERY codegen_ready_inst (non_param_insts bb)` by
    metis_tac[regional_non_param_insts_ready] >>
  `EVERY inst_wf (non_param_insts bb)` by
    metis_tac[regional_non_param_insts_wf] >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def, LET_THM] >> pairarg_tac >>
  `~MEM dead_stack_marker ps1.ps_stack` by
    metis_tac[regional_dfs_params_marker_free] >>
  `~ps1.ps_cleanup_promised` by
    (Cases_on `bb = HD fn.fn_blocks` >> gvs[] >>
     metis_tac[prepare_params_plan_promised, SND]) >>
  gvs[] >> pairarg_tac >>
  `~MEM dead_stack_marker ps2.ps_stack` by
    (Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) = 1` >>
     gvs[] >> metis_tac[regional_ret_cleanup_marker_free]) >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
  metis_tac[regional_insts_marker_free]
QED

Theorem regional_dfs_marker_mutual[local]:
  codegen_ready_fn fn /\ lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET ==>
  (!wl visited ps.
    dfs_aux_call (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth sb ctr) wl visited ps ==>
    dfs_aux_call (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth sb ctr) wl visited ps /\
    LENGTH wl <= 1 /\
    ((!l. MEM l wl ==> ~cfg_path (cfg_analyze fn) l target) \/
      ~MEM dead_stack_marker ps.ps_stack)) /\
  (!ss sp succs visited ps.
    dfs_succs_call (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth sb ctr) ss sp succs visited ps ==>
    dfs_succs_call (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth sb ctr) ss sp succs visited ps /\
    ((!l. MEM l succs ==> ~cfg_path (cfg_analyze fn) l target) \/
      ~MEM dead_stack_marker ss))
Proof
  strip_tac >> ho_match_mp_tac dfs_aux_call_ind >> rpt conj_tac
  >- (rpt strip_tac >> simp[dfs_aux_call_entry, init_cleanup_plan_state_def,
        stackPlanTypesTheory.init_plan_state_def])
  >- (rpt gen_tac >> strip_tac >>
      (conj_tac >- metis_tac[dfs_aux_call_visited] >>
       rename1 `LENGTH (lbl::tail) <= 1` >>
       Cases_on `tail` >> gvs[]))
  >- (rpt gen_tac >> strip_tac >>
      (conj_tac >- metis_tac[dfs_aux_call_missing] >>
       rename1 `LENGTH (lbl::tail) <= 1` >>
       Cases_on `tail` >> gvs[]))
  >- (rpt gen_tac >> strip_tac >>
      (conj_tac >- metis_tac[dfs_aux_call_succs] >>
       Cases_on `cfg_path (cfg_analyze fn) lbl target`
       >- (disj2_tac >>
           `~MEM dead_stack_marker ps.ps_stack` by metis_tac[MEM] >>
           `dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
             (init_cleanup_plan_state ch growth sb ctr) lbl ps` by
             (simp[dfs_block_state_def] >> metis_tac[]) >>
           metis_tac[regional_dfs_block_marker_free]) >>
       disj1_tac >> metis_tac[cfg_path_predecessor_closed]))
  >- (rpt gen_tac >> strip_tac >>
      (conj_tac >- metis_tac[dfs_aux_call_rest] >>
       rename1 `LENGTH (lbl::tail) <= 1` >>
       Cases_on `tail` >> gvs[]))
  >- (rpt gen_tac >> strip_tac >>
      (conj_tac >- metis_tac[dfs_aux_call_branch] >>
       simp[] >> metis_tac[MEM]))
  >> rpt gen_tac >> strip_tac >>
  (conj_tac >- metis_tac[dfs_aux_call_sibling] >>
   metis_tac[MEM])
QED

Theorem regional_ret_reaching_dfs_marker_free:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  dfs_block_state (liveness_analyze fn) dfg cfg fn
    (init_cleanup_plan_state ch growth sb ctr) lbl ps /\
  cfg_path cfg lbl target ==>
  ~MEM dead_stack_marker ps.ps_stack
Proof
  simp[dfs_block_state_def] >> rpt strip_tac >> gvs[] >>
  drule_all (cj 1 regional_dfs_marker_mutual) >>
  simp[] >> metis_tac[]
QED

Theorem regional_lineage_cleanup_upper:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  lineage_entry lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    pred bb.bb_label ps /\
  cfg_preds_of cfg bb.bb_label = [pred] /\
  1 < LENGTH (cfg_succs_of cfg pred) /\
  ~MEM dead_stack_marker ps.ps_stack /\ ~ps.ps_cleanup_promised /\
  (!n. ~cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth
    cfg fn bb n) /\
  clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
  EVERY (\op. ?v. op = Var v /\ MEM v (input_vars_from pred
    bb.bb_instructions (live_vars_at lv bb.bb_label 0))) qs.ps_stack
Proof
  strip_tac >> drule_all lineage_entry_inventory >> strip_tac >>
  `FILTER (\op. op <> dead_stack_marker) ps.ps_stack = ps.ps_stack` by
    simp[FILTER_EQ_ID, EVERY_MEM] >>
  `ALL_DISTINCT ps.ps_stack` by
    gvs[generated_plan_state_wf_marked_def] >>
  `EVERY (\op. ?v. op = Var v /\ MEM v
    (live_vars_at lv pred (LENGTH pred_bb.bb_instructions))) ps.ps_stack` by
    (simp[EVERY_MEM] >> metis_tac[]) >>
  drule_all inventory_cleanup_support >> simp[]
QED

Theorem regional_dfs_single_pred_exit:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn sb ctr =
    SOME (fops,pend) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ cfg_preds_of cfg lbl = [pred] /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) lbl ds /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) pred pin /\
  generate_block_plan lv dfg cfg fn pred_bb pin = SOME (bops,pout) ==>
  ds.ps_stack = pout.ps_stack /\ ds.ps_spilled = pout.ps_spilled
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `dfs_block_state _ _ _ _ _ lbl ds` mp_tac >>
  disch_then (strip_assume_tac o MATCH_MP dfs_block_state_inverse_origin)
  >- (drule regional_entry_no_preds >>
      gvs[fn_entry_label_def, entry_block_def, AllCaseEqs()]) >>
  rename1 `MEM lbl (cfg_succs_of (cfg_analyze fn) origin)` >>
  `MEM origin (cfg_preds_of (cfg_analyze fn) lbl)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  gvs[] >>
  rename1 `generate_block_plan _ _ _ _ pred_bb origin_in = SOME _` >>
  `origin_in = pin` by metis_tac[dfs_block_state_unique] >> gvs[]
QED

Theorem regional_single_successor_recompute_out:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) lbl /\
  cfg_succs_of (cfg_analyze fn) lbl = [succ] ==>
  set (df_at [] (liveness_recompute fn) lbl
    (LENGTH (liveness_instrs fn.fn_blocks lbl))) =
  set (liveness_edge_transfer fn.fn_blocks succ lbl
    (df_at [] (liveness_recompute fn) succ 0))
Proof
  strip_tac >> drule_all liveness_recompute_convergence >>
  simp[livenessDefsTheory.same_vars_set, liveness_out_def, list_union_set]
QED

Theorem regional_single_successor_exit_input:
  wf_function fn /\ cfg_reachable_of (cfg_analyze fn) lbl /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block succ fn.fn_blocks = SOME target /\
  cfg_succs_of (cfg_analyze fn) lbl = [succ] ==>
  set (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) SUBSET
  set (input_vars_from lbl target.bb_instructions
    (live_vars_at (liveness_analyze fn) succ 0))
Proof
  strip_tac >> drule_all regional_single_successor_recompute_out >>
  simp[liveness_instrs_def, liveness_edge_transfer_def,
    liveness_analyze_def, live_vars_at_def]
QED

Theorem regional_selected_phi_upper_step:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfg = dfg_build_function fn /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb i ps /\
  EVERY (\op. ?v. op = Var v /\ U i v) ps.ps_stack /\
  (!src out. MEM (Var src) (EL i bb.bb_instructions).inst_operands /\
    MEM (Var src) ps.ps_stack /\ (EL i bb.bb_instructions).inst_outputs = [out] ==>
    (!v. U i v /\ v <> src ==> U (i+1) v) /\
    (MEM out (live_vars_at (liveness_analyze fn) bb.bb_label (i+1)) ==> U (i+1) out)) /\
  generate_phi_plan (EL i bb.bb_instructions)
    (live_vars_at (liveness_analyze fn) bb.bb_label (i+1)) F ps = (ops,qs) ==>
  EVERY (\op. ?v. op = Var v /\ U (i+1) v) qs.ps_stack
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM (EL i bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    metis_tac[collect_phis_index, EL_MEM] >>
  `DROP i (collect_phis bb.bb_instructions) =
    EL i bb.bb_instructions :: DROP (i+1) (collect_phis bb.bb_instructions)` by
    metis_tac[DROP_CONS_EL, collect_phis_index, arithmeticTheory.ADD1] >>
  drule_all regional_indexed_phi_output >> strip_tac >>
  `?src. MEM (Var src) (EL i bb.bb_instructions).inst_operands /\
    MEM (Var src) ps.ps_stack /\
    (!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands /\
      (MEM (Var v) ps.ps_stack \/ Var v IN FDOM ps.ps_spilled) ==> v = src)` by
    (gvs[regional_selected_phi_inv_def] >> metis_tac[MEM]) >>
  `?d. stack_get_phi_depth
    (FILTER is_var_operand (EL i bb.bb_instructions).inst_operands) ps.ps_stack = SOME d /\
    d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = Var src` by
    (irule regional_phi_physical_depth >> metis_tac[]) >>
  `~MEM src (live_vars_at (liveness_analyze fn) bb.bb_label (i+1))` by
    (irule regional_ready_phi_source_dead >> simp[] >>
     gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var]) >>
  `~MEM (Var out) ps.ps_stack` by
    metis_tac[regional_selected_phi_output_absent, MEM] >>
  `ALL_DISTINCT (FILTER (\op. op <> dead_stack_marker) ps.ps_stack)` by
    gvs[regional_selected_phi_inv_def, generated_plan_state_wf_marked_def] >>
  drule_all inventory_marked_phi_mem >> disch_tac >>
  gvs[EVERY_MEM] >> metis_tac[]
QED

Theorem regional_selected_phi_upper_prefix:
  !j i ps ops qs fn bb dfg cfg sb U.
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  dfg = dfg_build_function fn /\
  i+j <= LENGTH (collect_phis bb.bb_instructions) /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb i ps /\
  EVERY (\op. ?v. op = Var v /\ U i v) ps.ps_stack /\
  (!t src out. i <= t /\ t < i+j /\
    MEM (Var src) (EL t bb.bb_instructions).inst_operands /\ U t src /\
    (EL t bb.bb_instructions).inst_outputs = [out] ==>
    (!v. U t v /\ v <> src ==> U (t+1) v) /\
    (MEM out (live_vars_at (liveness_analyze fn) bb.bb_label (t+1)) ==> U (t+1) out)) /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label
    F 0 (LENGTH bb.bb_instructions) i j (DROP i bb.bb_instructions) ps =
      SOME (ops,qs) ==>
  EVERY (\op. ?v. op = Var v /\ U (i+j) v) qs.ps_stack
Proof
  Induct_on `j` >- simp[generate_block_insts_prefix_def] >>
  rpt gen_tac >> strip_tac >>
  `i < LENGTH (collect_phis bb.bb_instructions)` by decide_tac >>
  `i < LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` current_collect_phis_length) >> decide_tac) >>
  `DROP i bb.bb_instructions = EL i bb.bb_instructions :: DROP (i+1) bb.bb_instructions` by
    metis_tac[DROP_CONS_EL, arithmeticTheory.ADD1] >>
  `(EL i bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[collect_phis_index, collect_phis_mem, EL_MEM] >>
  `DROP (i+1) bb.bb_instructions = [] ==> i+1 = LENGTH bb.bb_instructions` by
    (simp[DROP_EQ_NIL] >> decide_tac) >>
  `i+1 <= LENGTH bb.bb_instructions` by decide_tac >>
  `live_vars_at (liveness_analyze fn) bb.bb_label
    (if DROP (i+1) bb.bb_instructions = [] then LENGTH bb.bb_instructions else i+1) =
    live_vars_at (liveness_analyze fn) bb.bb_label (i+1)` by metis_tac[] >>
  qpat_x_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once generate_block_insts_prefix_def, generate_inst_plan_def,
    is_pre_codegen_opcode_def, LET_THM] >>
  simp[AllCaseEqs()] >> strip_tac >>
  `i+1 = LENGTH bb.bb_instructions \/ ~(LENGTH bb.bb_instructions <= i+1)` by decide_tac >>
  gvs[] >> rename1 `generate_phi_plan _ _ _ ps = (step_ops,mid)` >>
  `regional_selected_phi_inv (liveness_analyze fn) (dfg_build_function fn) sb bb (i+1) mid` by
    (irule regional_selected_phi_inv_step >> simp[] >>
     qexistsl [`F`, `step_ops`, `ps`] >> gvs[]) >>
  `EVERY (\op. ?v. op = Var v /\ U (i+1) v) mid.ps_stack` by
    (irule regional_selected_phi_upper_step >>
     rpt (first_assum $ irule_at Any) >>
     qpat_x_assum `!a b c d e f g h p. _` kall_tac >>
     TRY (qexists_tac `step_ops`) >> simp[] >>
     rpt gen_tac >> strip_tac >>
     `U i src` by
       (qpat_x_assum `EVERY _ ps.ps_stack` mp_tac >>
        simp[EVERY_MEM] >> disch_then (qspec_then `Var src` mp_tac) >> simp[]) >>
     qpat_x_assum `!t src out. _` (qspec_then `i` mp_tac) >>
     simp[] >> disch_then (qspec_then `src` mp_tac) >> simp[]) >>
  `i + SUC j = (i+1)+j` by decide_tac >>
  pop_assum SUBST1_TAC >> first_x_assum irule >> simp[] >>
  qexistsl [`bb`, `cfg`, `fn`, `rest_ops`, `mid`, `sb`] >>
  gvs[arithmeticTheory.ADD1] >> rpt strip_tac >>
  qpat_x_assum `!t src out. _` (qspecl_then [`t`, `src`, `out`] mp_tac) >>
  simp[]
QED

Definition regional_phi_remaining_source_def:
  regional_phi_remaining_source bb i v <=>
    MEM (Var v) (FLAT (MAP (\p. p.inst_operands)
      (DROP i (collect_phis bb.bb_instructions))))
End

Definition regional_phi_upper_family_def:
  regional_phi_upper_family lv bb selected i v <=>
    (MEM v (live_vars_at lv bb.bb_label i) /\
     ~regional_phi_remaining_source bb i v) \/
    (selected v /\ regional_phi_remaining_source bb i v)
End

Theorem regional_phi_upper_family_endpoint:
  ~regional_phi_remaining_source bb (LENGTH (collect_phis bb.bb_instructions)) v /\
  (regional_phi_upper_family lv bb selected (LENGTH (collect_phis bb.bb_instructions)) v <=>
   MEM v (live_vars_at lv bb.bb_label (LENGTH (collect_phis bb.bb_instructions))))
Proof
  simp[regional_phi_remaining_source_def, regional_phi_upper_family_def]
QED

Theorem regional_phi_remaining_source_step:
  i < LENGTH (collect_phis bb.bb_instructions) ==>
  (regional_phi_remaining_source bb i v <=>
   MEM (Var v) (EL i bb.bb_instructions).inst_operands \/
   regional_phi_remaining_source bb (i+1) v)
Proof
  strip_tac >>
  `DROP i (collect_phis bb.bb_instructions) =
    EL i (collect_phis bb.bb_instructions) ::
    DROP (i+1) (collect_phis bb.bb_instructions)` by
    metis_tac[DROP_CONS_EL, arithmeticTheory.ADD1] >>
  simp[regional_phi_remaining_source_def, collect_phis_index]
QED

Theorem regional_phi_remaining_source_mem:
  regional_phi_remaining_source bb i v ==>
  ?phi. MEM phi (collect_phis bb.bb_instructions) /\ MEM v (inst_uses phi)
Proof
  simp[regional_phi_remaining_source_def, MEM_FLAT, MEM_MAP] >>
  rpt strip_tac >> rename1 `MEM phi (DROP i (collect_phis bb.bb_instructions))` >>
  qexists_tac `phi` >>
  gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
  drule rich_listTheory.MEM_DROP_IMP >> simp[]
QED

Theorem regional_phi_upper_family_live_step[local]:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label i) /\
  ~regional_phi_remaining_source bb i v ==>
  MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (i+1)) /\
  ~regional_phi_remaining_source bb (i+1) v
Proof
  strip_tac >>
  `~MEM (Var v) (EL i bb.bb_instructions).inst_operands /\
   ~regional_phi_remaining_source bb (i+1) v` by
    metis_tac[regional_phi_remaining_source_step] >>
  `~MEM v (inst_uses (EL i bb.bb_instructions))` by
    gvs[inst_uses_def, passSharedDefsTheory.MEM_operand_vars_eq_Var] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by
    metis_tac[fn_reachable_in_cfg_dfs_pre] >>
  `SUC i <= LENGTH bb.bb_instructions` by
    (mp_tac (Q.SPEC `bb.bb_instructions` current_collect_phis_length) >> decide_tac) >>
  drule live_vars_at_transfer >> simp[] >>
  disch_then (qspecl_then [`bb.bb_label`, `bb`, `i`] mp_tac) >>
  simp[livenessDefsTheory.liveness_transfer_def, arithmeticTheory.ADD1] >>
  strip_tac >> gvs[live_update_mem]
QED

Theorem regional_phi_upper_family_transition:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  t < LENGTH (collect_phis bb.bb_instructions) /\
  (!phi x y. MEM phi (collect_phis bb.bb_instructions) /\ selected x /\ selected y /\
    MEM (Var x) phi.inst_operands /\ MEM (Var y) phi.inst_operands ==> x=y) /\
  MEM (Var src) (EL t bb.bb_instructions).inst_operands /\
  regional_phi_upper_family (liveness_analyze fn) bb selected t src /\
  (EL t bb.bb_instructions).inst_outputs = [out] ==>
  (!v. regional_phi_upper_family (liveness_analyze fn) bb selected t v /\ v<>src ==>
    regional_phi_upper_family (liveness_analyze fn) bb selected (t+1) v) /\
  (MEM out (live_vars_at (liveness_analyze fn) bb.bb_label (t+1)) ==>
    regional_phi_upper_family (liveness_analyze fn) bb selected (t+1) out)
Proof
  strip_tac >>
  `MEM (EL t bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    metis_tac[collect_phis_index, EL_MEM] >>
  `regional_phi_remaining_source bb t src` by
    metis_tac[regional_phi_remaining_source_step] >>
  `selected src` by gvs[regional_phi_upper_family_def] >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `regional_phi_remaining_source bb t v`
      >- (`selected v` by gvs[regional_phi_upper_family_def] >>
          `~MEM (Var v) (EL t bb.bb_instructions).inst_operands` by metis_tac[] >>
          `regional_phi_remaining_source bb (t+1) v` by
            metis_tac[regional_phi_remaining_source_step] >>
          simp[regional_phi_upper_family_def]) >>
      `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label t)` by
        gvs[regional_phi_upper_family_def] >>
      drule_all regional_phi_upper_family_live_step >>
      simp[regional_phi_upper_family_def]) >>
  strip_tac >>
  `~regional_phi_remaining_source bb (t+1) out` by
    (strip_tac >> drule regional_phi_remaining_source_mem >> strip_tac >>
     `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
     `MEM out (EL t bb.bb_instructions).inst_outputs` by simp[] >>
     drule_all regional_phi_output_not_phi_source >> simp[]) >>
  simp[regional_phi_upper_family_def]
QED

Theorem regional_selected_phi_initial_unique[local]:
  regional_selected_phi_inv lv dfg sb bb 0 ps ==>
  !phi x y. MEM phi (collect_phis bb.bb_instructions) /\
    MEM (Var x) ps.ps_stack /\ MEM (Var y) ps.ps_stack /\
    MEM (Var x) phi.inst_operands /\ MEM (Var y) phi.inst_operands ==> x=y
Proof
  simp[regional_selected_phi_inv_def] >> rpt strip_tac >>
  qpat_x_assum `!phi. _` drule >> strip_tac >> metis_tac[]
QED

Theorem regional_selected_phi_upper_complete:
  codegen_ready_fn fn /\ fn_reachable fn bb.bb_label /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\ dfg = dfg_build_function fn /\
  regional_selected_phi_inv (liveness_analyze fn) dfg sb bb 0 ps0 /\
  EVERY (\op. ?v. op = Var v /\
    (regional_phi_remaining_source bb 0 v \/
     MEM v (live_vars_at (liveness_analyze fn) bb.bb_label 0))) ps0.ps_stack /\
  generate_block_insts_prefix (liveness_analyze fn) dfg cfg fn bb.bb_label F 0
    (LENGTH bb.bb_instructions) 0 (LENGTH (collect_phis bb.bb_instructions))
    bb.bb_instructions ps0 = SOME (ops,qs) ==>
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at (liveness_analyze fn) bb.bb_label
      (LENGTH (collect_phis bb.bb_instructions)))) qs.ps_stack
Proof
  strip_tac >>
  `EVERY (\op. ?v. op = Var v /\
     regional_phi_upper_family (liveness_analyze fn) bb
       (\v. MEM (Var v) ps0.ps_stack) 0 v) ps0.ps_stack` by
    (gvs[EVERY_MEM, regional_phi_upper_family_def] >> metis_tac[]) >>
  `EVERY (\op. ?v. op = Var v /\
     regional_phi_upper_family (liveness_analyze fn) bb
       (\v. MEM (Var v) ps0.ps_stack)
       (LENGTH (collect_phis bb.bb_instructions)) v) qs.ps_stack` suffices_by
    simp[regional_phi_upper_family_endpoint] >>
  irule (Q.SPECL [`LENGTH (collect_phis bb.bb_instructions)`, `0`]
    regional_selected_phi_upper_prefix |> SIMP_RULE (srw_ss()) []) >> simp[] >>
  qexistsl [`bb`, `cfg`, `fn`, `ops`, `ps0`, `sb`] >> gvs[] >>
  rpt gen_tac >> strip_tac >> irule regional_phi_upper_family_transition >> simp[] >>
  drule regional_selected_phi_initial_unique >> simp[]
QED

Theorem regional_dfs_incoming_lineage_entry:
  cfg = cfg_analyze fn /\ codegen_ready_fn fn /\
  dfs_block_state lv dfg cfg fn ps0 succ ds /\ fn_entry_label fn <> SOME succ ==>
  ?pred pred_bb. lookup_block pred fn.fn_blocks = SOME pred_bb /\
    fn_reachable fn pred /\ MEM succ (cfg_succs_of cfg pred) /\
    lineage_entry lv dfg cfg fn ps0 pred succ ds
Proof
  strip_tac >> drule dfs_block_state_inverse_origin >> strip_tac >> gvs[] >>
  `fn_reachable fn pred` by
    (drule_all dfs_block_state_cfg_reachable >>
     `wf_function fn` by gvs[codegen_ready_fn_def] >>
     metis_tac[fn_reachable_cfg_analyze]) >>
  `lineage_entry lv dfg (cfg_analyze fn) fn ps0 pred succ ds` by
    (`ds = ds with <| ps_stack := pout.ps_stack;
                      ps_spilled := pout.ps_spilled |>` by
       gvs[plan_state_component_equality] >>
     pop_assum SUBST1_TAC >> irule dfs_edge_lineage_entry >> simp[] >>
     metis_tac[]) >>
  metis_tac[]
QED

Theorem regional_lineage_single_successor_upper:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\ fn_reachable fn pred /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lineage_entry lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    pred bb.bb_label ps /\ cfg_succs_of cfg pred = [bb.bb_label] /\
  ~MEM dead_stack_marker ps.ps_stack ==>
  EVERY (\op. ?v. op = Var v /\ MEM v
    (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0))) ps.ps_stack
Proof
  strip_tac >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `cfg_reachable_of (cfg_analyze fn) pred` by metis_tac[fn_reachable_cfg_analyze] >>
  drule_all lineage_entry_inventory >> strip_tac >> gvs[] >>
  drule_all regional_single_successor_exit_input >>
  simp[pred_setTheory.SUBSET_DEF] >> strip_tac >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  `op <> dead_stack_marker` by metis_tac[] >>
  qpat_x_assum `!op. _ \/ _ ==> _` (qspec_then `op` mp_tac) >> simp[] >>
  strip_tac >> goal_assum (drule_at Any) >> gvs[]
QED

Theorem regional_lineage_single_successor_cleanup_upper:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\ fn_reachable fn pred /\
  lookup_block pred fn.fn_blocks = SOME pred_bb /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  lineage_entry lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    pred bb.bb_label ps /\ cfg_succs_of cfg pred = [bb.bb_label] /\
  ~MEM dead_stack_marker ps.ps_stack /\ cfg_preds_of cfg bb.bb_label = [pred] /\
  clean_stack_plan lv cfg fn bb ps = (ops,qs) ==>
  EVERY (\op. ?v. op = Var v /\ MEM v
    (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0))) qs.ps_stack
Proof
  strip_tac >>
  `qs = ps` by gvs[clean_stack_plan_def] >> gvs[] >>
  irule regional_lineage_single_successor_upper >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem regional_lineage_join_upper[local]:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  LENGTH (cfg_preds_of cfg bb.bb_label) <> 1 /\
  lineage_entry lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr)
    pred bb.bb_label ps /\ ~MEM dead_stack_marker ps.ps_stack ==>
  EVERY (\op. ?v. op = Var v /\ MEM v
    (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0))) ps.ps_stack
Proof
  strip_tac >> drule_all lineage_entry_join_stack >> strip_tac >> gvs[] >>
  `pre = []` by
    (Cases_on `pre` >> gvs[EVERY_DEF]) >>
  gvs[EVERY_MAP, combinTheory.o_DEF, EVERY_MEM]
QED

Theorem regional_dfs_nonentry_cleanup_upper:
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\ lookup_block target fn.fn_blocks = SOME retbb /\
  MEM ret_inst retbb.bb_instructions /\ ret_inst.inst_opcode = RET /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ fn_entry_label fn <> SOME lbl /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth sb ctr) lbl ps /\
  cfg_path cfg lbl target /\
  (if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then clean_stack_plan lv cfg fn bb ps
   else ([],ps)) = (clean_ops,qs) ==>
  ?pred pred_bb. lookup_block pred fn.fn_blocks = SOME pred_bb /\
    fn_reachable fn pred /\ MEM lbl (cfg_succs_of cfg pred) /\
    EVERY (\op. ?v. op = Var v /\ MEM v
      (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0))) qs.ps_stack
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[lookup_block_label] >>
  `~MEM dead_stack_marker ps.ps_stack` by
    (irule regional_ret_reaching_dfs_marker_free >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all ret_region_dfs_block_unpromised >> strip_tac >>
  drule_all regional_dfs_incoming_lineage_entry >> strip_tac >>
  qexistsl [`pred`,`pred_bb`] >> simp[] >>
  Cases_on `LENGTH (cfg_preds_of cfg bb.bb_label) = 1`
  >- (gvs[] >>
      `cfg_preds_of (cfg_analyze fn) bb.bb_label = [pred]` by
        (`MEM pred (cfg_preds_of (cfg_analyze fn) bb.bb_label)` by
           metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
         Cases_on `cfg_preds_of (cfg_analyze fn) bb.bb_label` >> gvs[] >>
         rename1 `LENGTH rest = 0` >> Cases_on `rest` >> gvs[]) >>
      Cases_on `LENGTH (cfg_succs_of (cfg_analyze fn) pred) = 1`
      >- (`cfg_succs_of (cfg_analyze fn) pred = [bb.bb_label]` by
            (Cases_on `cfg_succs_of (cfg_analyze fn) pred` >> gvs[] >>
             rename1 `LENGTH rest = 0` >> Cases_on `rest` >> gvs[]) >>
          irule regional_lineage_single_successor_cleanup_upper >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      `1 < LENGTH (cfg_succs_of (cfg_analyze fn) pred)` by
        (Cases_on `cfg_succs_of (cfg_analyze fn) pred` >> gvs[] >>
         rename1 `rest <> []` >> Cases_on `rest` >> gvs[]) >>
      `!n. ~cleanup_elision_safe ps.ps_cleanup_height ps.ps_cleanup_growth
        (cfg_analyze fn) fn bb n` by
        (gen_tac >> irule (cj 2 ret_reaching_cleanup_not_safe) >>
         goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      irule regional_lineage_cleanup_upper >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[] >> irule regional_lineage_join_upper >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem regional_entry_dfs_initial:
  codegen_ready_fn fn /\
  dfs_block_state lv dfg (cfg_analyze fn) fn ps0 (HD fn.fn_blocks).bb_label ps ==>
  ps = ps0
Proof
  strip_tac >> drule dfs_block_state_inverse_origin >> strip_tac >> gvs[] >>
  drule regional_entry_no_preds >>
  metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond, MEM]
QED

Theorem regional_prepare_params_initial_upper:
  codegen_ready_fn fn /\
  prepare_params_plan (liveness_analyze fn) fn
    ((init_cleanup_plan_state ch growth sb ctr) with
      <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) = (ops,qs) ==>
  EVERY (\op. ?v. op = Var v /\
    MEM v (live_vars_at (liveness_analyze fn) (HD fn.fn_blocks).bb_label
      (LENGTH (get_params (HD fn.fn_blocks).bb_instructions)))) qs.ps_stack
Proof
  strip_tac >> drule_all regional_prepare_params_initial_membership >>
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `op` mp_tac) >> simp[] >>
  strip_tac >> gvs[MEM_MAP, operand_to_string_def]
QED

Theorem regional_edge_input_upper_source:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  MEM v (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0)) ==>
  regional_phi_remaining_source bb 0 v \/ MEM v (live_vars_at lv bb.bb_label 0)
Proof
  strip_tac >> drule input_vars_from_phi_correct_proof >> strip_tac
  >- simp[] >>
  disj1_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  drule_all ready_phi_use_location >> strip_tac >>
  `MEM inst (collect_phis bb.bb_instructions)` by metis_tac[EL_MEM] >>
  `MEM (Var v) inst.inst_operands` by metis_tac[phi_pairs_mem_var] >>
  simp[regional_phi_remaining_source_def, MEM_FLAT, MEM_MAP] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem regional_edge_input_upper:
  codegen_ready_fn fn /\ lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  EVERY (\op. ?v. op = Var v /\ MEM v
    (input_vars_from pred bb.bb_instructions (live_vars_at lv bb.bb_label 0))) ps.ps_stack ==>
  EVERY (\op. ?v. op = Var v /\
    (regional_phi_remaining_source bb 0 v \/ MEM v (live_vars_at lv bb.bb_label 0))) ps.ps_stack
Proof
  simp[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  drule_all regional_edge_input_upper_source >> simp[]
QED

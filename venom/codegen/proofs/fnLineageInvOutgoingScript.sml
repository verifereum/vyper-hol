Theory fnLineageInvOutgoing
Ancestors planWfMarked codegenReadyCompute fnLineageInvDFSResources fnLineageInvBoundary fnLineageInvBlock fnPlanLineage fnPlanPrefix fnLineageInvEdgeFacts fnPlanLineageInventory stackPlanGen stackPlanTypes list pred_set

Theorem lineage_state_outgoing_inventory:
  !fn dfg ch growth base ctr.
    codegen_ready_fn fn ==>
    !lbl P. lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth base ctr) lbl P ==>
    !bb next h promised ops A.
      lookup_block lbl fn.fn_blocks = SOME bb /\
      MEM next (cfg_succs_of (cfg_analyze fn) lbl) /\
      generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
        (P with <|ps_cleanup_height := h; ps_cleanup_promised := promised|>) = SOME (ops,A)
      ==>
      lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) lbl
        (LENGTH bb.bb_instructions)))) A
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac lineage_state_ind >> conj_tac
  >- (rpt strip_tac >>
      drule regional_entry_structure >> strip_tac >>
      `bb = HD fn.fn_blocks` by
        metis_tac[venomExecPropsTheory.lookup_block_label, optionTheory.SOME_11] >>
      `fn.fn_blocks <> []` by
        gvs[codegen_ready_fn_def, venomWfTheory.wf_function_def,
            venomWfTheory.fn_has_entry_def] >>
      `cfg_preds_of (cfg_analyze fn) bb.bb_label = []` by
        metis_tac[fnPlanLineageCallersTheory.ready_entry_no_clean] >>
      `lbl = bb.bb_label` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
      gvs[] >>
      qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
      simp[init_cleanup_plan_state_def] >>
      disch_tac >>
      drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
        (SRULE [init_cleanup_plan_state_def] analyzed_parameter_entry_block_inventory) >>
      simp[] >> disch_then (qspec_then `next` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  `lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) lbl
      (LENGTH bb.bb_instructions)))) ps_after` by
    (first_x_assum drule_all >> simp[]) >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by metis_tac[dfs_block_state_cfg_reachable] >>
  `cfg_reachable_of (cfg_analyze fn) lbl'` by metis_tac[dfs_block_state_cfg_reachable] >>
  `wf_function fn` by gvs[codegen_ready_fn_def] >>
  `fn_reachable fn lbl'` by metis_tac[fn_reachable_cfg_analyze] >>
  `fn_entry_label fn <> SOME lbl'` by metis_tac[ready_incoming_nonentry] >>
  drule regional_entry_structure >> strip_tac >>
  `bb'.bb_label = lbl'` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `bb' <> HD fn.fn_blocks` by metis_tac[] >>
  qpat_assum `dfs_block_state _ _ _ _ _ lbl' ps_succ`
    (mp_then Any mp_tac dfs_block_state_resources) >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `generate_block_plan _ _ _ _ bb' start` >>
  `lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) lbl
      (LENGTH bb.bb_instructions)))) start` by
    (gvs[Abbr `start`, lineage_inventory_def, lineage_core_def] >> metis_tac[]) >>
  `plan_slots_bounded base' start /\ spill_alloc_layout_wf start.ps_alloc start.ps_spilled` by
    (gvs[Abbr `start`, planSpillBoundsTheory.plan_slots_bounded_def] >> metis_tac[]) >>
  `generated_plan_state_wf_marked base' start` by
    (drule lineage_inventory_splice_marked_iff >>
     disch_then (qspecl_then [`start`, `base'`] mp_tac) >>
     simp[Abbr `start`, planSpillBoundsTheory.plan_slots_bounded_def] >>
     metis_tac[planSpillBoundsTheory.plan_slots_bounded_def]) >>
  `MEM lbl (cfg_preds_of (cfg_analyze fn) lbl')` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  Cases_on `LENGTH (cfg_preds_of (cfg_analyze fn) lbl') = 1`
  >- (`cfg_preds_of (cfg_analyze fn) lbl' = [lbl]` by
        (Cases_on `cfg_preds_of (cfg_analyze fn) lbl'` >> gvs[LENGTH_EQ_NUM]) >>
      drule_all analyzed_singleton_outgoing_block_inventory >> simp[]) >>
  `1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl')` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) lbl'` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  `LENGTH (cfg_succs_of (cfg_analyze fn) lbl) <= 1` by
    (qpat_x_assum `codegen_ready_fn fn` mp_tac >>
     simp[codegen_ready_fn_def, cfgDefsTheory.cfg_is_normalized_def] >>
     strip_tac >>
     `MEM bb' fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
     qpat_x_assum `!b. MEM b fn.fn_blocks ==> _`
       (qspec_then `bb'` mp_tac) >> simp[]) >>
  `cfg_succs_of (cfg_analyze fn) lbl = [lbl']` by
    (Cases_on `cfg_succs_of (cfg_analyze fn) lbl` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  drule_all lineage_inventory_core_budget >> strip_tac >>
  `?B. generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
      (P with <|ps_cleanup_height := ch'; ps_cleanup_promised := promised|>) = SOME (block_ops,B) /\
      start.ps_stack = B.ps_stack /\ start.ps_spilled = B.ps_spilled` by
    (qexists_tac `ps_after` >> simp[Abbr `start`]) >>
  metis_tac[analyzed_join_outgoing_block_inventory]
QED

Theorem lineage_entry_exact_inventory:
  !fn dfg ch growth base ctr pred bb succ ps.
    codegen_ready_fn fn /\ lookup_block pred fn.fn_blocks = SOME bb /\
    lineage_entry (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth base ctr) pred succ ps ==>
    lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) pred
      (LENGTH bb.bb_instructions)))) ps
Proof
  rpt gen_tac >> simp[lineage_entry_def] >> strip_tac >> gvs[] >>
  drule_all lineage_state_outgoing_inventory >>
  strip_tac >>
  gvs[lineage_inventory_def, lineage_core_def] >> metis_tac[]
QED

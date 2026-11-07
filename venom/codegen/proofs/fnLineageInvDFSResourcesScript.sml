Theory fnLineageInvDFSResources
Ancestors fnPlanLineage fnLineageInvOwnerOrigin fnLineageInvBoundary fnLineageInvBlock reorderSim planSpillBounds list

Theorem residual_budget_wf_alloc_extension:
  !base pending A D.
    residual_budget_wf base pending A /\
    D.ps_stack = A.ps_stack /\ D.ps_spilled = A.ps_spilled /\
    D.ps_alloc.sa_spill_base = A.ps_alloc.sa_spill_base /\
    D.ps_alloc.sa_free_slots = A.ps_alloc.sa_free_slots /\
    A.ps_alloc.sa_next_offset <= D.ps_alloc.sa_next_offset ==>
    residual_budget_wf base pending D
Proof
  rpt gen_tac >> strip_tac >>
  `spill_alloc_layout_wf D.ps_alloc D.ps_spilled` by
    (irule spill_alloc_layout_wf_extension >>
     qexists_tac `A.ps_alloc` >> gvs[residual_budget_wf_def]) >>
  gvs[residual_budget_wf_def, plan_slots_bounded_def,
      alloc_slots_bounded_def, EVERY_MEM] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem dfs_calls_inventory_resources[local]:
  !fn dfg ch growth base ctr.
  codegen_ready_fn fn ==>
  (!wl visited ps.
    dfs_aux_call (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth base ctr) wl visited ps ==>
    dfs_aux_call (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth base ctr) wl visited ps /\
    (wl = [] \/ ?lbl. wl = [lbl] /\
      ((fn_entry_label fn = SOME lbl /\
        ps = init_cleanup_plan_state ch growth base ctr) \/
       ?pred pb B ops A.
         fn_reachable fn pred /\
         dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
           (init_cleanup_plan_state ch growth base ctr) pred B /\
         lookup_block pred fn.fn_blocks = SOME pb /\
         MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
         generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb B = SOME (ops,A) /\
         ps.ps_stack = A.ps_stack /\ ps.ps_spilled = A.ps_spilled /\
         lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) pred
           (LENGTH pb.bb_instructions)))) ps /\
         ?m core. lineage_core m core ps /\ EVERY is_var_operand core /\
           residual_budget_wf base [] (ps with ps_stack := core)))) /\
  (!stk spills succs visited ps.
    dfs_succs_call (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth base ctr) stk spills succs visited ps ==>
    dfs_succs_call (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth base ctr) stk spills succs visited ps /\
    !lbl. MEM lbl succs ==>
      ?pred pb B ops A.
         fn_reachable fn pred /\
        dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
          (init_cleanup_plan_state ch growth base ctr) pred B /\
        lookup_block pred fn.fn_blocks = SOME pb /\
        MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
        generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb B = SOME (ops,A) /\
        stk = A.ps_stack /\ spills = A.ps_spilled /\
        lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) pred
          (LENGTH pb.bb_instructions))))
          (ps with <|ps_stack := stk; ps_spilled := spills|>) /\
        ?m core. lineage_core m core (ps with <|ps_stack := stk; ps_spilled := spills|>) /\
          EVERY is_var_operand core /\
          residual_budget_wf base []
            (ps with <|ps_stack := core; ps_spilled := spills|>))
Proof
  rpt gen_tac >> disch_tac >> ho_match_mp_tac dfs_aux_call_ind >>
  rpt strip_tac >> gvs[] >>
  simp[dfs_aux_call_rules]
  >- metis_tac[dfs_aux_call_visited]
  >- metis_tac[dfs_aux_call_visited]
  >- metis_tac[dfs_aux_call_succs]
  >- (drule fnPlanPrefixTheory.regional_entry_structure >> strip_tac >>
      `bb = HD fn.fn_blocks` by
        metis_tac[venomExecPropsTheory.lookup_block_label, optionTheory.SOME_11] >>
      `fn.fn_blocks <> []` by
        gvs[stackPlanGenTheory.codegen_ready_fn_def, venomWfTheory.wf_function_def,
            venomWfTheory.fn_has_entry_def] >>
      `cfg_preds_of (cfg_analyze fn) bb.bb_label = []` by
        metis_tac[fnPlanLineageCallersTheory.ready_entry_no_clean] >>
      `lbl = bb.bb_label` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
      `LENGTH (cfg_preds_of (cfg_analyze fn) bb.bb_label) <> 1` by simp[] >>
      gvs[] >>
      drule_at (Pat `generate_block_plan _ _ _ _ _ _ = _`)
        analyzed_parameter_entry_block_inventory >> simp[] >>
      disch_then (qspec_then `lbl''` mp_tac) >> simp[] >> strip_tac >>
      qexistsl_tac [`(HD fn.fn_blocks).bb_label`, `HD fn.fn_blocks`,
        `init_cleanup_plan_state ch growth base' ctr`, `block_ops`, `ps'`] >>
      simp[dfs_block_state_def] >> metis_tac[])
  >- metis_tac[dfs_aux_call_succs]
  >- (`wf_function fn` by gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
      `fn_reachable fn lbl` by
        metis_tac[codegenReadyComputeTheory.fn_cfg_edge_cfg_analyze,
                  venomExecProofsTheory.fn_reachable_step] >>
      `cfg_reachable_of (cfg_analyze fn) pred` by
        metis_tac[codegenReadyComputeTheory.fn_reachable_cfg_analyze] >>
      `fn_entry_label fn <> SOME lbl` by
        metis_tac[fnLineageInvEdgeFactsTheory.ready_incoming_nonentry] >>
      drule fnPlanPrefixTheory.regional_entry_structure >> strip_tac >>
      `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
      `bb <> HD fn.fn_blocks` by metis_tac[] >>
      Cases_on `cfg_preds_of (cfg_analyze fn) lbl = [pred]`
      >- (`generated_plan_state_wf_marked base' ps` by
            (drule lineage_inventory_splice_marked_iff >>
             disch_then (qspecl_then [`ps`, `base'`] mp_tac) >> simp[NoAsms] >>
             `plan_slots_bounded base' ps /\
              doSwapSim$spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled` by
               (qpat_x_assum `residual_budget_wf _ _ _` mp_tac >>
                simp[reorderSimTheory.residual_budget_wf_def,
                     planSpillBoundsTheory.plan_slots_bounded_def] >> metis_tac[]) >>
             simp[]) >>
          drule_all analyzed_singleton_outgoing_block_inventory >> strip_tac >>
          qexistsl_tac [`lbl`, `bb`, `ps`, `block_ops`, `ps'`] >>
          simp[dfs_block_state_def] >> metis_tac[]) >>
      `MEM pred (cfg_preds_of (cfg_analyze fn) lbl)` by
        metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
      `1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl)` by
        (Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> gvs[] >>
         Cases_on `t` >> gvs[]) >>
      `LENGTH (cfg_succs_of (cfg_analyze fn) pred) <= 1` by
        (`cfg_is_normalized (cfg_analyze fn) fn` by
           gvs[stackPlanGenTheory.codegen_ready_fn_def] >>
         `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
         qpat_x_assum `cfg_is_normalized _ _` mp_tac >>
         simp[NoAsms, cfgDefsTheory.cfg_is_normalized_def] >>
         disch_then (qspec_then `bb` mp_tac) >> simp[]) >>
      `cfg_succs_of (cfg_analyze fn) pred = [lbl]` by
        (Cases_on `cfg_succs_of (cfg_analyze fn) pred` >> gvs[] >>
         Cases_on `t` >> gvs[]) >>
      `lbl <> (HD fn.fn_blocks).bb_label` by metis_tac[] >>
      drule_at (Pat `generate_block_plan _ _ _ _ _ _ = SOME (_,_)`)
        analyzed_join_outgoing_block_inventory >> simp[] >>
      disch_then (drule_at (Pat `lineage_inventory _ _`)) >> simp[] >>
      disch_then (drule_at (Pat `residual_budget_wf _ _ _`)) >> simp[] >>
      disch_then (qspec_then `lbl''` mp_tac) >> simp[] >>
      disch_then (qspecl_then [`B`, `ops`, `m`] mp_tac) >>
      impl_tac >- (simp[] >> qexists_tac `A` >> simp[]) >> strip_tac >>
      qexistsl_tac [`lbl`, `bb`, `ps`, `block_ops`, `ps'`] >>
      simp[dfs_block_state_def] >> metis_tac[])
  >- metis_tac[dfs_aux_call_rest]
  >- metis_tac[dfs_aux_call_rest]
  >- metis_tac[dfs_aux_call_branch]
  >- metis_tac[dfs_aux_call_sibling] >>
  drule (cj 1 allocMonoTheory.fn_plan_aux_alloc_mono) >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`pred`, `pb`, `B`, `ops`, `A`] >> simp[] >>
  conj_tac
  >- (gvs[fnPlanLineageInventoryTheory.lineage_inventory_def,
          fnPlanLineageInventoryTheory.lineage_core_def] >> metis_tac[]) >>
  qexistsl_tac [`m`, `core`] >>
  simp[fnPlanLineageInventoryTheory.lineage_core_def] >>
  conj_tac >- gvs[fnPlanLineageInventoryTheory.lineage_core_def] >>
  irule residual_budget_wf_alloc_extension >>
  qexists_tac `ps with <|ps_stack := core; ps_spilled := spills|>` >> simp[]
QED

Theorem dfs_block_state_resources:
  !fn dfg ch growth base ctr lbl D.
    codegen_ready_fn fn /\
    dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
      (init_cleanup_plan_state ch growth base ctr) lbl D ==>
    plan_slots_bounded base D /\
    spill_alloc_layout_wf D.ps_alloc D.ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  gvs[dfs_block_state_def] >>
  drule_all (cj 1 dfs_calls_inventory_resources) >> strip_tac >> gvs[] >>
  gvs[residual_budget_wf_def, plan_slots_bounded_def,
      stackPlanGenTheory.init_cleanup_plan_state_def,
      stackPlanTypesTheory.init_plan_state_def,
      alloc_slots_bounded_def, doSwapSimTheory.spill_alloc_layout_wf_def,
      stackPlanTypesTheory.init_spill_alloc_def] >> metis_tac[]
QED

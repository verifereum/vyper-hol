Theory fnPlanLineageJoinEntry
Ancestors
  fnPlanLineagePhiRealization fnPlanLineagePhiActivation fnPlanLineageEdge
  fnPlanLineagePhiMaps codegenReadyCompute stackPlanGen venomWf venomExecProps
  livenessTransferProofs list finite_map

Theorem analyzed_edge_phi_matching_total:
  codegen_ready_fn fn /\ lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) pred) ==>
  !v i. FLOOKUP (FST (build_phi_maps pred (collect_phis sb.bb_instructions))) v = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps pred (collect_phis sb.bb_instructions))) i)
Proof
  rpt strip_tac >> irule build_phi_maps_matching_total >>
  conj_tac >- (qexists_tac `v` >> simp[]) >>
  `MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `fn_cfg_edge fn pred sb.bb_label` by metis_tac[fn_cfg_edge_cfg_analyze] >>
  simp[EVERY_MEM] >> rpt strip_tac >>
  drule collect_phis_mem >> strip_tac >>
  `phi_edge_uses_wf fn sb phi` by
    (gvs[def_dominates_uses_def] >>
     first_x_assum (qspecl_then [`sb`, `phi`] mp_tac) >> simp[]) >>
  gvs[phi_edge_uses_wf_def] >>
  first_x_assum (qspec_then `pred` mp_tac) >> simp[] >>
  strip_tac >> PairCases_on `p` >> gvs[] >> metis_tac[]
QED

Theorem successful_join_edges_native_cells:
  !fn p pb q qb succ sb dfg psP0 opsP psP psQ0 opsQ psQ.
  codegen_ready_fn fn /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block q fn.fn_blocks = SOME qb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) p) /\
  MEM succ (cfg_succs_of (cfg_analyze fn) q) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb psP0 =
    SOME (opsP, psP) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn qb psQ0 =
    SOME (opsQ, psQ) ==>
  ?cells prefixP prefixQ.
    cells = MAP
      (phi_slot_cell (SND (build_phi_maps p (collect_phis sb.bb_instructions)))
                     (SND (build_phi_maps q (collect_phis sb.bb_instructions))))
      (phi_slot_trace (FST (build_phi_maps p (collect_phis sb.bb_instructions)))
        (live_vars_at (liveness_analyze fn) succ 0)) /\
    phi_uses_disjoint (collect_phis sb.bb_instructions) /\
    (!v i. FLOOKUP (FST (build_phi_maps p (collect_phis sb.bb_instructions))) v = SOME i ==>
      IS_SOME (FLOOKUP (SND (build_phi_maps p (collect_phis sb.bb_instructions))) i) /\
      IS_SOME (FLOOKUP (SND (build_phi_maps q (collect_phis sb.bb_instructions))) i)) /\
    phi_origin_classes (native_phi_class p (collect_phis sb.bb_instructions)) cells /\
    psP.ps_stack = prefixP ++ MAP (phi_cell_value T) cells /\
    psQ.ps_stack = prefixQ ++ MAP (phi_cell_value F) cells /\
    MAP (phi_cell_value T) cells = MAP Var
      (input_vars_from p sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))
Proof
  rpt gen_tac >> strip_tac >>
  `?prefixP. psP.ps_stack = prefixP ++ MAP Var
    (input_vars_from p sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))` by
    (irule generate_block_plan_join_edge_suffix >> goal_assum (drule_at Any) >> simp[]) >>
  `?prefixQ. psQ.ps_stack = prefixQ ++ MAP Var
    (input_vars_from q sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))` by
    (irule generate_block_plan_join_edge_suffix >> goal_assum (drule_at Any) >> simp[]) >>
  `phi_uses_disjoint (collect_phis sb.bb_instructions)` by
    (`MEM sb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
     `~EVERY (\b. NULL (collect_phis b.bb_instructions)) fn.fn_blocks` by
       (simp[listTheory.EVERY_MEM, listTheory.EXISTS_MEM, combinTheory.o_DEF] >>
        qexists_tac `sb` >> simp[]) >>
     gvs[codegen_ready_fn_def, phi_operands_ready_def, phi_block_ready_def,
         listTheory.EVERY_MEM] >> metis_tac[]) >>
  `!v i. FLOOKUP (FST (build_phi_maps p (collect_phis sb.bb_instructions))) v = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps p (collect_phis sb.bb_instructions))) i)` by
    (rpt strip_tac >> irule analyzed_edge_phi_matching_total >>
     conj_tac >- metis_tac[] >> qexistsl_tac [`fn`, `succ`] >> simp[]) >>
  `!v i. FLOOKUP (FST (build_phi_maps p (collect_phis sb.bb_instructions))) v = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps q (collect_phis sb.bb_instructions))) i)` by
    (rpt strip_tac >> irule analyzed_edge_phi_matching_total >>
     conj_tac >- metis_tac[build_phi_maps_source_independent] >>
     qexistsl_tac [`fn`, `succ`] >> simp[]) >>
  qabbrev_tac `cells = MAP
    (phi_slot_cell (SND (build_phi_maps p (collect_phis sb.bb_instructions)))
                   (SND (build_phi_maps q (collect_phis sb.bb_instructions))))
    (phi_slot_trace (FST (build_phi_maps p (collect_phis sb.bb_instructions)))
       (live_vars_at (liveness_analyze fn) succ 0))` >>
  qexistsl_tac [`cells`, `prefixP`, `prefixQ`] >>
  conj_tac >- simp[Abbr `cells`] >>
  conj_tac >- simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (simp[Abbr `cells`] >> irule native_slot_cells_classes >> simp[] >> metis_tac[]) >>
  `MAP (phi_cell_value T) cells = MAP Var
    (input_vars_from p sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))` by
    (simp[Abbr `cells`] >> irule input_vars_from_cells_projection >> simp[] >> metis_tac[]) >>
  `MAP (phi_cell_value F) cells = MAP Var
    (input_vars_from q sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))` by
    (simp[Abbr `cells`] >> irule input_vars_from_cells_projection >>
     conj_tac >- metis_tac[] >>
     `FST (build_phi_maps p (collect_phis sb.bb_instructions)) =
      FST (build_phi_maps q (collect_phis sb.bb_instructions))` by
       metis_tac[build_phi_maps_source_independent] >>
     simp[]) >>
  simp[]
QED

Theorem successful_join_edges_common_cells_projection:
  !fn p pb q qb succ sb dfg psP0 opsP psP psQ0 opsQ psQ.
  codegen_ready_fn fn /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block q fn.fn_blocks = SOME qb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) p) /\
  MEM succ (cfg_succs_of (cfg_analyze fn) q) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb psP0 =
    SOME (opsP, psP) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn qb psQ0 =
    SOME (opsQ, psQ) ==>
  ?cells prefixP prefixQ.
    phi_origin_classes (native_phi_class p (collect_phis sb.bb_instructions)) cells /\
    psP.ps_stack = prefixP ++ MAP (phi_cell_value T) cells /\
    psQ.ps_stack = prefixQ ++ MAP (phi_cell_value F) cells /\
    MAP (phi_cell_value T) cells = MAP Var
      (input_vars_from p sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))
Proof
  metis_tac[successful_join_edges_native_cells]
QED

Theorem successful_join_edges_common_cells:
  !fn p pb q qb succ sb dfg psP0 opsP psP psQ0 opsQ psQ.
  codegen_ready_fn fn /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block q fn.fn_blocks = SOME qb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) p) /\
  MEM succ (cfg_succs_of (cfg_analyze fn) q) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb psP0 =
    SOME (opsP, psP) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn qb psQ0 =
    SOME (opsQ, psQ) ==>
  ?cells prefixP prefixQ.
    phi_origin_classes (native_phi_class p (collect_phis sb.bb_instructions)) cells /\
    psP.ps_stack = prefixP ++ MAP (phi_cell_value T) cells /\
    psQ.ps_stack = prefixQ ++ MAP (phi_cell_value F) cells
Proof
  metis_tac[successful_join_edges_common_cells_projection]
QED

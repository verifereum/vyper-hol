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

Theorem successful_join_edge_selected_phi_present:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 =
    SOME (ops,ps) /\
  j < LENGTH (collect_phis bb.bb_instructions) /\
  FIND (\(l,w). l = pred)
    (phi_pairs (EL j (collect_phis bb.bb_instructions)).inst_operands) =
    SOME (pred,v) ==>
  MEM (Var v) (EL j (collect_phis bb.bb_instructions)).inst_operands /\
  MEM (Var v) ps.ps_stack
Proof
  strip_tac >>
  `MEM v (input_vars_from pred bb.bb_instructions
    (live_vars_at (liveness_analyze fn) lbl 0))` by
    (irule reachable_phi_incoming_activated >>
     goal_assum (drule_at Any) >> simp[] >> qexists_tac `j` >> simp[]) >>
  `?prefix. ps.ps_stack = prefix ++ MAP Var
    (input_vars_from pred bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0))` by
    (irule generate_block_plan_join_edge_suffix >>
     goal_assum (drule_at Any) >> simp[]) >>
  conj_tac
  >- (drule venomExecPropsTheory.FIND_MEM >>
      metis_tac[cfgNormBaseTheory.phi_pairs_mem_var]) >>
  simp[listTheory.MEM_MAP]
QED

Theorem successful_join_edge_phi_candidate:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 =
    SOME (ops,ps) /\
  j < LENGTH (collect_phis bb.bb_instructions) ==>
  ?v. MEM (Var v) (EL j (collect_phis bb.bb_instructions)).inst_operands /\
      MEM (Var v) ps.ps_stack
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `MEM (EL j (collect_phis bb.bb_instructions)) bb.bb_instructions /\
   (EL j (collect_phis bb.bb_instructions)).inst_opcode = PHI` by
    metis_tac[listTheory.EL_MEM, collect_phis_mem] >>
  `phi_edge_uses_wf fn bb (EL j (collect_phis bb.bb_instructions))` by
    (gvs[def_dominates_uses_def] >>
     first_x_assum (qspecl_then [`bb`, `EL j (collect_phis bb.bb_instructions)`] mp_tac) >> simp[]) >>
  `fn_cfg_edge fn pred bb.bb_label` by metis_tac[fn_cfg_edge_cfg_analyze] >>
  `?v. MEM (pred,v) (phi_pairs (EL j (collect_phis bb.bb_instructions)).inst_operands)` by
    (gvs[phi_edge_uses_wf_def] >> metis_tac[pairTheory.PAIR]) >>
  `FIND (\(l,w). l = pred)
    (phi_pairs (EL j (collect_phis bb.bb_instructions)).inst_operands) = SOME (pred,v)` by
    (gvs[phi_edge_uses_wf_def] >>
     drule_all (Q.ISPEC `FST : string # string -> string` distinct_key_FIND_member) >>
     simp[pairTheory.LAMBDA_PROD]) >>
  qexists_tac `v` >> irule successful_join_edge_selected_phi_present >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem successful_join_edge_phi_candidate_origin:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 =
    SOME (ops,ps) /\
  j < LENGTH (collect_phis bb.bb_instructions) /\
  (!v. MEM (Var v) ps.ps_stack ==>
    ?db di. MEM db fn.fn_blocks /\ MEM di db.bb_instructions /\
            MEM v di.inst_outputs /\ MEM db.bb_label visited) ==>
  ?v db di.
    MEM (Var v) (EL j (collect_phis bb.bb_instructions)).inst_operands /\
    MEM (Var v) ps.ps_stack /\ MEM db fn.fn_blocks /\
    MEM di db.bb_instructions /\ MEM v di.inst_outputs /\
    MEM db.bb_label visited
Proof
  strip_tac >>
  `?v. MEM (Var v) (EL j (collect_phis bb.bb_instructions)).inst_operands /\
       MEM (Var v) ps.ps_stack` by
    (irule successful_join_edge_phi_candidate >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

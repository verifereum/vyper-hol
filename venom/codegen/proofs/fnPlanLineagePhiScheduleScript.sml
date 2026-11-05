Theory fnPlanLineagePhiSchedule
Ancestors
  fnPlanLineagePhiTemporal fnPlanLineagePhiClasses fnPlanLineageJoinEntry
  fnPlanLineagePhiActivation fnPlanLineagePhiMaps venomExecProps venomWf stackPlanGen
  codegenReadyCompute livenessTransferProofs

Theorem reachable_native_phi_cells_coverage:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  MAP (phi_cell_value T) cells = MAP Var
    (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)) ==>
  !i. i < LENGTH (collect_phis bb.bb_instructions) ==>
    ?cell. MEM cell cells /\
      native_phi_class pred (collect_phis bb.bb_instructions) (phi_cell_value T cell) = SOME i
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ def_dominates_uses fn` by gvs[codegen_ready_fn_def] >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    metis_tac[ready_block_phi_uses_disjoint] >>
  `MEM (EL i (collect_phis bb.bb_instructions)) bb.bb_instructions /\
   (EL i (collect_phis bb.bb_instructions)).inst_opcode = PHI` by
    metis_tac[listTheory.EL_MEM, collect_phis_mem] >>
  `phi_edge_uses_wf fn bb (EL i (collect_phis bb.bb_instructions))` by
    (gvs[def_dominates_uses_def] >>
     first_x_assum (qspecl_then [`bb`, `EL i (collect_phis bb.bb_instructions)`] mp_tac) >> simp[]) >>
  `fn_cfg_edge fn pred bb.bb_label` by metis_tac[fn_cfg_edge_cfg_analyze] >>
  `?v. MEM (pred,v) (phi_pairs (EL i (collect_phis bb.bb_instructions)).inst_operands)` by
    (gvs[phi_edge_uses_wf_def] >> metis_tac[pairTheory.PAIR]) >>
  `FIND (\(l,w). l = pred)
     (phi_pairs (EL i (collect_phis bb.bb_instructions)).inst_operands) = SOME (pred,v)` by
    (gvs[phi_edge_uses_wf_def] >>
     drule_all (Q.ISPEC `FST : string # string -> string` distinct_key_FIND_member) >> simp[pairTheory.LAMBDA_PROD]) >>
  `MEM v (input_vars_from pred bb.bb_instructions
     (live_vars_at (liveness_analyze fn) lbl 0))` by
    (irule reachable_phi_incoming_activated >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `i` >> simp[]) >>
  `MEM (Var v) (MAP (phi_cell_value T) cells)` by
    (simp[] >> irule listTheory.MEM_MAP_f >> simp[]) >>
  gvs[listTheory.MEM_MAP] >> qexists_tac `y` >> simp[] >>
  qpat_x_assum `Var v = phi_cell_value T y` (fn th => rewrite_tac[GSYM th]) >>
  simp[native_phi_class_def] >>
  drule build_phi_maps_operand_class >>
  disch_then (qspecl_then [`v`, `pred`, `i`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem analyzed_native_phi_schedule_ready:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
  MAP (phi_cell_value T) cells = MAP Var
    (input_vars_from pred bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  phi_origin_classes (native_phi_class pred (collect_phis bb.bb_instructions)) cells ==>
  ?cells_end. phi_origin_schedule_ready
    (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) lbl (SUC i), halting))
      (collect_phis bb.bb_instructions)) prefixP prefixQ cells cells_end /\
    phi_origin_classes (native_phi_class pred (collect_phis bb.bb_instructions)) cells_end
Proof
  strip_tac >>
  Cases_on `NULL (collect_phis bb.bb_instructions)`
  >- gvs[listTheory.NULL_EQ, phi_origin_schedule_ready_def] >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `wf_function fn /\ fn_inst_wf fn /\ phi_operands_ready fn` by gvs[codegen_ready_fn_def] >>
  `phi_block_ready (liveness_analyze fn) bb` by
    (`~EVERY (\b. NULL (collect_phis b.bb_instructions)) fn.fn_blocks` by
       (simp[listTheory.EVERY_MEM, listTheory.EXISTS_MEM, combinTheory.o_DEF] >>
        qexists_tac `bb` >> simp[]) >>
     gvs[phi_operands_ready_def, listTheory.EVERY_MEM]) >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    metis_tac[ready_block_phi_uses_disjoint] >>
  `EVERY (\phi. inst_wf phi) (collect_phis bb.bb_instructions)` by
    (gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[collect_phis_mem]) >>
  `EVERY (\phi. phi_well_formed phi.inst_operands) (collect_phis bb.bb_instructions)` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     `phi.inst_opcode = PHI /\ inst_wf phi` by metis_tac[collect_phis_mem] >>
     metis_tac[cfgNormBaseTheory.inst_wf_phi_well_formed]) >>
  irule phi_origin_schedule_from_classes >> simp[] >> qexists_tac `0` >>
  simp[indexedListsTheory.LENGTH_MAPi] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      gvs[indexedListsTheory.EL_MAPi] >>
      conj_tac >- (irule native_phi_class_exact >> simp[]) >>
      conj_tac
      >- (`MEM (EL i (collect_phis bb.bb_instructions)) (collect_phis bb.bb_instructions)` by
            simp[listTheory.EL_MEM] >>
          `inst_wf (EL i (collect_phis bb.bb_instructions)) /\
           (EL i (collect_phis bb.bb_instructions)).inst_opcode = PHI` by
            metis_tac[listTheory.EVERY_MEM, collect_phis_mem] >>
          drule_all cfgNormBaseTheory.inst_wf_phi_well_formed >> strip_tac >>
          `MEM (HD (EL i (collect_phis bb.bb_instructions)).inst_outputs)
             (EL i (collect_phis bb.bb_instructions)).inst_outputs` by
            (Cases_on `(EL i (collect_phis bb.bb_instructions)).inst_outputs` >> gvs[]) >>
          metis_tac[reachable_native_phi_output_class_none]) >>
      rpt strip_tac >> Cases_on `op` >>
      gvs[native_phi_class_def, stackPlanTypesTheory.operand_to_string_def] >>
      `native_phi_class pred (collect_phis bb.bb_instructions) (Var s) = SOME i` by
        simp[native_phi_class_def] >>
      drule analyzed_native_phi_class_dead_after >> simp[] >>
      qexistsl_tac [`s`, `pred`, `i`, `bb`] >> simp[]) >>
  rpt strip_tac >> irule reachable_native_phi_cells_coverage >>
  goal_assum (drule_at Any) >> simp[] >> qexistsl_tac [`entry`, `fn`, `lbl`] >> simp[]
QED

Theorem successful_join_edges_phi_schedule_ready:
  !fn p pb q qb succ sb dfg psP0 opsP psP psQ0 opsQ psQ entry halting.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn succ /\ succ <> entry /\ MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block q fn.fn_blocks = SOME qb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) p) /\
  MEM succ (cfg_succs_of (cfg_analyze fn) q) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb psP0 = SOME (opsP, psP) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn qb psQ0 = SOME (opsQ, psQ) ==>
  ?cells prefixP prefixQ cells_end.
    phi_origin_classes (native_phi_class p (collect_phis sb.bb_instructions)) cells /\
    psP.ps_stack = prefixP ++ MAP (phi_cell_value T) cells /\
    psQ.ps_stack = prefixQ ++ MAP (phi_cell_value F) cells /\
    MAP (phi_cell_value T) cells = MAP Var
      (input_vars_from p sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0)) /\
    phi_origin_schedule_ready
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) prefixP prefixQ cells cells_end /\
    phi_origin_classes (native_phi_class p (collect_phis sb.bb_instructions)) cells_end
Proof
  rpt gen_tac >> strip_tac >>
  `?cells prefixP prefixQ.
    phi_origin_classes (native_phi_class p (collect_phis sb.bb_instructions)) cells /\
    psP.ps_stack = prefixP ++ MAP (phi_cell_value T) cells /\
    psQ.ps_stack = prefixQ ++ MAP (phi_cell_value F) cells /\
    MAP (phi_cell_value T) cells = MAP Var
      (input_vars_from p sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))` by
    (irule successful_join_edges_common_cells_projection >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`dfg`, `opsP`, `opsQ`, `psP0`, `psQ0`, `q`, `qb`] >> simp[]) >>
  drule_all analyzed_native_phi_schedule_ready >>
  disch_then (qspecl_then [`prefixQ`, `prefixP`, `halting`] strip_assume_tac) >>
  qexistsl_tac [`cells`, `prefixP`, `prefixQ`, `cells_end`] >> simp[]
QED

Theorem successful_join_edges_phi_state_replay:
  !fn p pb q qb succ sb dfg psP0 opsP psP psQ0 opsQ psQ entry halting rsP rsQ.
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn succ /\ succ <> entry /\ MEM succ (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block p fn.fn_blocks = SOME pb /\
  lookup_block q fn.fn_blocks = SOME qb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) p) /\
  MEM succ (cfg_succs_of (cfg_analyze fn) q) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb psP0 = SOME (opsP, psP) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn qb psQ0 = SOME (opsQ, psQ) /\
  rsP.ps_stack = psP.ps_stack /\ rsQ.ps_stack = psQ.ps_stack /\
  rsP.ps_alloc = rsQ.ps_alloc ==>
  ?cells_end prefixP prefixQ ops al.
    phi_origin_classes (native_phi_class p (collect_phis sb.bb_instructions)) cells_end /\
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) rsP =
      (ops, rsP with <|ps_stack := prefixP ++ MAP (phi_cell_value T) cells_end; ps_alloc := al|>) /\
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) rsQ =
      (ops, rsQ with <|ps_stack := prefixQ ++ MAP (phi_cell_value F) cells_end; ps_alloc := al|>)
Proof
  rpt gen_tac >> strip_tac >>
  `?cells prefixP prefixQ cells_end.
    phi_origin_classes (native_phi_class p (collect_phis sb.bb_instructions)) cells /\
    psP.ps_stack = prefixP ++ MAP (phi_cell_value T) cells /\
    psQ.ps_stack = prefixQ ++ MAP (phi_cell_value F) cells /\
    MAP (phi_cell_value T) cells = MAP Var
      (input_vars_from p sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0)) /\
    phi_origin_schedule_ready
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) prefixP prefixQ cells cells_end /\
    phi_origin_classes (native_phi_class p (collect_phis sb.bb_instructions)) cells_end` by
    (irule successful_join_edges_phi_schedule_ready >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`dfg`, `opsP`, `opsQ`, `psP0`, `psQ0`, `q`, `qb`] >> simp[]) >>
  `rsP.ps_stack = prefixP ++ MAP (phi_cell_value T) cells /\
   rsQ.ps_stack = prefixQ ++ MAP (phi_cell_value F) cells` by simp[] >>
  drule_all phi_origin_schedule_state_replay >> strip_tac >>
  qexistsl_tac [`cells_end`, `prefixP`, `prefixQ`, `ops`, `al`] >> simp[]
QED

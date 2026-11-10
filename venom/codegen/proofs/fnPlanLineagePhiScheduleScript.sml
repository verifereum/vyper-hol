Theory fnPlanLineagePhiSchedule
Ancestors
  fnPlanLineagePhiTemporal fnPlanLineagePhiClasses fnPlanLineageJoinEntry
  fnPlanLineagePhiRealization fnPlanLineagePhiSlots fnPlanLineageEdge
  fnPlanLineagePhiActivation fnPlanLineagePhiMaps venomExecProps venomWf stackPlanGen
  codegenReadyCompute livenessTransferProofs fnPlanLineageCallers
  livenessDefs venomInst list fnPlanLineageLiveness fnPlanLineagePhiSuffixResources
  fnPlanLineageNativeTargets

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

Theorem successful_join_edge_native_phi_coverage:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn succ /\ succ <> entry /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  ~NULL (collect_phis sb.bb_instructions) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 =
    SOME (ops,psAfter) ==>
  !i. i < LENGTH (collect_phis sb.bb_instructions) ==>
    ?op. MEM op psAfter.ps_stack /\
      native_phi_class pred (collect_phis sb.bb_instructions) op = SOME i
Proof
  strip_tac >> drule_all generate_block_plan_join_edge_suffix >> strip_tac >>
  `MAP (phi_cell_value T)
     (MAP PhiCommon (MAP Var (input_vars_from pred sb.bb_instructions
       (live_vars_at (liveness_analyze fn) succ 0)))) =
   MAP Var (input_vars_from pred sb.bb_instructions
       (live_vars_at (liveness_analyze fn) succ 0))` by
    simp[listTheory.MAP_MAP_o, combinTheory.o_DEF, phi_cell_value_def,
         ETA_AX] >>
  mp_tac (Q.INST [`cells` |-> `MAP PhiCommon (MAP Var
    (input_vars_from pred sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0)))`,
    `lbl` |-> `succ`, `bb` |-> `sb`] reachable_native_phi_cells_coverage) >>
  simp[] >> rpt strip_tac >> first_x_assum drule >>
  simp[listTheory.MEM_MAP, phi_cell_value_def] >> strip_tac >>
  gvs[phi_cell_value_def] >> goal_assum (drule_at Any) >>
  simp[phi_cell_value_def]
QED

Theorem analyzed_native_phi_schedule_classes:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
  !i inst next h.
    i < LENGTH (collect_phis bb.bb_instructions) /\
    EL i (MAPi (\j phi. (phi, live_vars_at (liveness_analyze fn) lbl (SUC j), (halting:bool)))
      (collect_phis bb.bb_instructions)) = (inst,next,h) ==>
    (!op. MEM op (FILTER is_var_operand inst.inst_operands) <=>
      native_phi_class pred (collect_phis bb.bb_instructions) op = SOME i) /\
    native_phi_class pred (collect_phis bb.bb_instructions)
      (Var (HD inst.inst_outputs)) = NONE /\
    (!op. native_phi_class pred (collect_phis bb.bb_instructions) op = SOME i ==>
      ~MEM (operand_to_string op) next)
Proof
  strip_tac >>
  Cases_on `NULL (collect_phis bb.bb_instructions)`
  >- gvs[listTheory.NULL_EQ] >>
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
  rpt gen_tac >> strip_tac >> gvs[indexedListsTheory.EL_MAPi] >>
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
  qexistsl_tac [`s`, `pred`, `i`, `bb`] >> simp[]
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
  irule phi_origin_schedule_from_classes >> simp[] >> qexists_tac `0` >>
  simp[indexedListsTheory.LENGTH_MAPi] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule analyzed_native_phi_schedule_classes >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`entry`, `fn`, `halting'`, `halting`, `lbl`] >> simp[]) >>
  rpt strip_tac >> irule reachable_native_phi_cells_coverage >>
  goal_assum (drule_at Any) >> simp[] >> qexistsl_tac [`entry`, `fn`, `lbl`] >> simp[]
QED

Theorem analyzed_native_phi_endpoint_class_dead:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
  phi_block_ready (liveness_analyze fn) bb /\
  native_phi_class p (collect_phis bb.bb_instructions) op = SOME i ==>
  ~MEM op (MAP Var (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))))
Proof
  strip_tac >> Cases_on `op` >> gvs[native_phi_class_def] >>
  rename1 `FLOOKUP _ v = SOME i` >>
  `native_phi_class p (collect_phis bb.bb_instructions) (Var v) = SOME i` by
    simp[native_phi_class_def] >>
  `phi_uses_disjoint (collect_phis bb.bb_instructions)` by
    gvs[phi_block_ready_def] >>
  drule_all native_phi_class_use >> strip_tac >>
  simp[listTheory.MEM_MAP] >> irule analyzed_native_phi_class_dead_range >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`i`, `p`] >> simp[]
QED

(* Backward demand across a native PHI needs only its singleton definition. *)
Theorem analyzed_native_phi_live_step:
  codegen_ready_fn fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  i < LENGTH (collect_phis bb.bb_instructions) /\
  MEM v (live_vars_at (liveness_analyze fn) lbl (SUC i)) ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl i) \/
  v = HD (EL i (collect_phis bb.bb_instructions)).inst_outputs
Proof
  strip_tac >>
  `wf_function fn /\ fn_inst_wf fn` by gvs[codegen_ready_fn_def] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `?rest. bb.bb_instructions = collect_phis bb.bb_instructions ++ rest` by
    metis_tac[collect_phis_prefix] >>
  `EL i bb.bb_instructions = EL i (collect_phis bb.bb_instructions) /\
   SUC i <= LENGTH bb.bb_instructions` by
    (conj_tac
     >- (qpat_assum `bb.bb_instructions = _`
           (fn th => simp[SimpLHS, Once th, listTheory.EL_APPEND_EQN])) >>
     qpat_x_assum `bb.bb_instructions = _` (fn th => once_rewrite_tac[th]) >>
     simp[] >> decide_tac) >>
  `inst_wf (EL i (collect_phis bb.bb_instructions)) /\
   (EL i (collect_phis bb.bb_instructions)).inst_opcode = PHI` by
    (gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >>
     metis_tac[listTheory.EL_MEM, collect_phis_mem]) >>
  drule livenessAnalysisPropsTheory.live_vars_at_transfer >>
  disch_then (qspecl_then [`lbl`, `bb`, `i`] mp_tac) >> simp[] >>
  `LENGTH (EL i (collect_phis bb.bb_instructions)).inst_outputs = 1` by
    gvs[inst_wf_def] >>
  Cases_on `(EL i (collect_phis bb.bb_instructions)).inst_outputs` >> gvs[] >>
  simp[liveness_transfer_def, livenessProofsTheory.live_update_mem,
       inst_defs_def, MEM_ordered_inst_uses] >> metis_tac[]
QED

Theorem analyzed_native_phi_schedule_live_member:
  codegen_ready_fn fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MAP (phi_cell_value T) cells = MAP Var
    (input_vars_from p bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)) /\
  phi_origin_schedule_ready
    (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) lbl (SUC i), halting))
      (collect_phis bb.bb_instructions)) prefixP prefixQ cells cells_end /\
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions))) ==>
  MEM (Var v) (MAP (phi_cell_value T) cells_end)
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `phi_block_ready (liveness_analyze fn) bb` by
    (Cases_on `NULL (collect_phis bb.bb_instructions)`
     >- gvs[listTheory.NULL_EQ, phi_block_ready_def, phi_uses_disjoint_def] >>
     `~EVERY (\b. NULL (collect_phis b.bb_instructions)) fn.fn_blocks` by
       (simp[listTheory.EVERY_MEM, listTheory.EXISTS_MEM, combinTheory.o_DEF] >>
        qexists_tac `bb` >> simp[]) >>
     gvs[codegen_ready_fn_def, phi_operands_ready_def, listTheory.EVERY_MEM]) >>
  `wf_function fn /\ phi_uses_disjoint (collect_phis bb.bb_instructions) /\ bb.bb_label = lbl` by
    (gvs[codegen_ready_fn_def, phi_block_ready_def] >> metis_tac[lookup_block_label]) >>
  `FLOOKUP (FST (build_phi_maps p (collect_phis bb.bb_instructions))) v = NONE` by
    (Cases_on `FLOOKUP (FST (build_phi_maps p (collect_phis bb.bb_instructions))) v` >> simp[] >>
     `native_phi_class p (collect_phis bb.bb_instructions) (Var v) = SOME x` by
       simp[native_phi_class_def] >>
     drule_all analyzed_native_phi_endpoint_class_dead >>
     simp[listTheory.MEM_MAP]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl 0) ==>
   MEM (Var v) (MAP (phi_cell_value T) cells)` by
    (strip_tac >> simp[] >>
     `LIST_ELEM_COUNT v (input_vars_from p bb.bb_instructions
       (live_vars_at (liveness_analyze fn) lbl 0)) =
      LIST_ELEM_COUNT v (live_vars_at (liveness_analyze fn) lbl 0)` by
       (irule input_vars_from_residual_count >> simp[] >> metis_tac[]) >>
     simp[listTheory.MEM_MAP] >>
     gvs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]) >>
  irule phi_origin_schedule_live_member >>
  rpt (goal_assum (drule_at Any)) >>
  simp[indexedListsTheory.LENGTH_MAPi] >>
  rpt gen_tac >> strip_tac >> gvs[indexedListsTheory.EL_MAPi] >>
  strip_tac >> irule analyzed_native_phi_live_step >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem analyzed_native_phi_schedule_observer_support:
  codegen_ready_fn fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MAP (phi_cell_value T) cells = MAP Var
    (input_vars_from p bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)) /\
  phi_origin_tagged (native_phi_class p (collect_phis bb.bb_instructions)) cells /\
  phi_origin_schedule_ready
    (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) lbl (SUC i), halting))
      (collect_phis bb.bb_instructions)) prefixP prefixQ cells cells_end /\
  EVERY (\c. ?op. c = PhiCommon op) cells_end /\
  (!inst. MEM inst (collect_phis bb.bb_instructions) ==> ~MEM v inst.inst_outputs) /\
  MEM (Var v) (MAP (phi_cell_value T) cells_end) ==>
  MEM v (live_vars_at (liveness_analyze fn) lbl
    (LENGTH (collect_phis bb.bb_instructions)))
Proof
  strip_tac >>
  `MEM (PhiCommon (Var v)) cells_end` by
    (gvs[listTheory.MEM_MAP, listTheory.EVERY_MEM] >>
     metis_tac[phi_cell_value_def]) >>
  `MEM (PhiCommon (Var v)) cells` by
    (irule phi_origin_schedule_common_origin >>
     rpt (goal_assum (drule_at Any)) >>
     simp[indexedListsTheory.MEM_MAPi] >> rpt strip_tac >> gvs[] >>
     `MEM (EL i (collect_phis bb.bb_instructions)) (collect_phis bb.bb_instructions)` by
       simp[listTheory.EL_MEM] >>
     `MEM bb fn.fn_blocks /\ fn_inst_wf fn` by
       metis_tac[lookup_block_MEM, codegen_ready_fn_def] >>
     `inst_wf (EL i (collect_phis bb.bb_instructions)) /\
      (EL i (collect_phis bb.bb_instructions)).inst_opcode = PHI` by
       (gvs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[collect_phis_mem]) >>
     gvs[inst_wf_def] >>
     Cases_on `(EL i (collect_phis bb.bb_instructions)).inst_outputs` >>
     gvs[] >> metis_tac[listTheory.MEM]) >>
  `FLOOKUP (FST (build_phi_maps p (collect_phis bb.bb_instructions))) v = NONE` by
    (qpat_x_assum `phi_origin_tagged _ _` mp_tac >>
     simp[phi_origin_tagged_def, listTheory.EVERY_MEM] >>
     disch_then (qspec_then `PhiCommon (Var v)` mp_tac) >>
     simp[native_phi_class_def]) >>
  `MEM (Var v) (MAP (phi_cell_value T) cells)` by
    (simp[listTheory.MEM_MAP] >> qexists_tac `PhiCommon (Var v)` >>
     simp[phi_cell_value_def]) >>
  `LIST_ELEM_COUNT v (input_vars_from p bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0)) =
   LIST_ELEM_COUNT v (live_vars_at (liveness_analyze fn) lbl 0)` by
    (irule input_vars_from_residual_count >> simp[] >>
     metis_tac[lookup_block_MEM, ready_block_phi_uses_disjoint]) >>
  `MEM v (input_vars_from p bb.bb_instructions
      (live_vars_at (liveness_analyze fn) lbl 0))` by
    (qpat_x_assum `MEM (Var v) (MAP (phi_cell_value T) cells)` mp_tac >>
     asm_rewrite_tac[] >> simp[listTheory.MEM_MAP]) >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl 0)` by
    metis_tac[rich_listTheory.LIST_ELEM_COUNT_MEM] >>
  metis_tac[ready_unrenamed_phi_partition]
QED

Theorem analyzed_native_slot_schedule_extinction:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) p) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  phi_uses_disjoint (collect_phis bb.bb_instructions) /\
  (!v i. MEM v livebase /\
    FLOOKUP (FST (build_phi_maps p (collect_phis bb.bb_instructions))) v = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps p (collect_phis bb.bb_instructions))) i) /\
    IS_SOME (FLOOKUP (SND (build_phi_maps q (collect_phis bb.bb_instructions))) i)) /\
  cells = MAP
    (phi_slot_cell (SND (build_phi_maps p (collect_phis bb.bb_instructions)))
                   (SND (build_phi_maps q (collect_phis bb.bb_instructions))))
    (phi_slot_trace (FST (build_phi_maps p (collect_phis bb.bb_instructions))) livebase) /\
  MAP (phi_cell_value T) cells = MAP Var
    (input_vars_from p bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)) ==>
  ?cells_end. phi_origin_schedule_ready
    (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) lbl (SUC i), halting))
      (collect_phis bb.bb_instructions)) prefixP prefixQ cells cells_end /\
    EVERY (\c. ?op. c = PhiCommon op) cells_end /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (collect_phis bb.bb_instructions))) ==>
      MEM (Var v) (MAP (phi_cell_value T) cells_end)) /\
    (!v. LIST_ELEM_COUNT (Var v) (MAP (phi_cell_value T) cells_end) <= 1) /\
    (!v. (!inst. MEM inst (collect_phis bb.bb_instructions) ==> ~MEM v inst.inst_outputs) /\
      ~MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (collect_phis bb.bb_instructions))) ==>
      ~MEM (Var v) (MAP (phi_cell_value T) cells_end))
Proof
  strip_tac >>
  `phi_origin_tagged (native_phi_class p (collect_phis bb.bb_instructions)) cells` by
    (qpat_assum `cells = _` SUBST1_TAC >> irule native_slot_cells_tagged >> simp[] >> metis_tac[]) >>
  `phi_origin_classes (native_phi_class p (collect_phis bb.bb_instructions)) cells` by
    metis_tac[phi_origin_tagged_classes] >>
  drule_all analyzed_native_phi_schedule_ready >>
  disch_then (qspecl_then [`prefixQ`, `prefixP`, `halting`] strip_assume_tac) >>
  qexists_tac `cells_end` >> simp[] >> conj_asm1_tac
  >- (irule phi_origin_tagged_schedule_common >>
      goal_assum (drule_at Any) >>
      qexistsl_tac [`native_phi_class p (collect_phis bb.bb_instructions)`, `0`] >>
      simp[indexedListsTheory.LENGTH_MAPi] >> conj_tac
      >- (rpt gen_tac >> strip_tac >> irule analyzed_native_phi_schedule_classes >>
          goal_assum (drule_at Any) >>
          qexistsl_tac [`entry`, `fn`, `halting'`, `halting`, `lbl`] >> simp[]) >>
      conj_tac >- (gvs[] >> simp[phi_slot_trace_origin_unique]) >>
      qpat_assum `cells = _` SUBST1_TAC >>
      simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
      rpt gen_tac >> strip_tac >> Cases_on `x` >> simp[phi_slot_cell_def] >>
      rpt strip_tac >> gvs[] >>
      rename1 `MEM (INR k) (phi_slot_trace _ _)` >>
      `?v. MEM v livebase /\
        FLOOKUP (FST (build_phi_maps p (collect_phis bb.bb_instructions))) v = SOME k` by
        (qpat_x_assum `MEM (INR k) _` mp_tac >> simp[phi_slot_trace_inr_mem]) >>
      metis_tac[build_phi_maps_operand_range]) >>
  conj_tac
  >- (rpt strip_tac >> irule analyzed_native_phi_schedule_live_member >>
      rpt (goal_assum (drule_at Any)) >> simp[]) >>
  conj_tac
  >- (gen_tac >> irule analyzed_phi_schedule_value_count_le_one >>
      rpt (goal_assum (drule_at Any)) >> metis_tac[]) >>
  rpt strip_tac >>
  `MEM v (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions)))` by
    (irule analyzed_native_phi_schedule_observer_support >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >> simp[]
QED

Theorem analyzed_native_slot_state_replay:
  codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
  fn_reachable fn lbl /\ lbl <> entry /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  MEM lbl (cfg_succs_of (cfg_analyze fn) p) /\
  MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  phi_uses_disjoint (collect_phis bb.bb_instructions) /\
  (!v i. MEM v livebase /\
    FLOOKUP (FST (build_phi_maps p (collect_phis bb.bb_instructions))) v = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps p (collect_phis bb.bb_instructions))) i) /\
    IS_SOME (FLOOKUP (SND (build_phi_maps q (collect_phis bb.bb_instructions))) i)) /\
  cells = MAP
    (phi_slot_cell (SND (build_phi_maps p (collect_phis bb.bb_instructions)))
                   (SND (build_phi_maps q (collect_phis bb.bb_instructions))))
    (phi_slot_trace (FST (build_phi_maps p (collect_phis bb.bb_instructions))) livebase) /\
  MAP (phi_cell_value T) cells = MAP Var
    (input_vars_from p bb.bb_instructions (live_vars_at (liveness_analyze fn) lbl 0)) /\
  ps.ps_stack = prefixP ++ MAP (phi_cell_value T) cells /\
  qs.ps_stack = prefixQ ++ MAP (phi_cell_value F) cells /\
  ps.ps_alloc = qs.ps_alloc ==>
  ?suffix ops al.
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) lbl (SUC i), halting))
        (collect_phis bb.bb_instructions)) ps =
      (ops, ps with <|ps_stack := prefixP ++ suffix; ps_alloc := al|>) /\
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) lbl (SUC i), halting))
        (collect_phis bb.bb_instructions)) qs =
      (ops, qs with <|ps_stack := prefixQ ++ suffix; ps_alloc := al|>) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (collect_phis bb.bb_instructions))) ==> MEM (Var v) suffix) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (collect_phis bb.bb_instructions))) ==> LIST_ELEM_COUNT (Var v) suffix = 1) /\
    (!v. (!inst. MEM inst (collect_phis bb.bb_instructions) ==> ~MEM v inst.inst_outputs) /\
      ~MEM v (live_vars_at (liveness_analyze fn) lbl
        (LENGTH (collect_phis bb.bb_instructions))) /\
      MEM v (input_vars_from p bb.bb_instructions
        (live_vars_at (liveness_analyze fn) lbl 0)) /\
      LIST_ELEM_COUNT (Var v) ps.ps_stack +
        (if Var v IN FDOM ps.ps_spilled then 1 else 0) <= 1 ==>
      ~MEM (Var v) (prefixP ++ suffix) /\ Var v NOTIN FDOM ps.ps_spilled)
Proof
  strip_tac >> drule_all analyzed_native_slot_schedule_extinction >>
  disch_then (qspecl_then [`prefixQ`, `prefixP`, `halting`] strip_assume_tac) >>
  `MAP (phi_cell_value T) cells_end = MAP (phi_cell_value F) cells_end` by
    (irule phi_common_cells_projection >> simp[]) >>
  drule_all phi_origin_schedule_state_replay >> strip_tac >>
  qexistsl_tac [`MAP (phi_cell_value T) cells_end`, `ops`, `al`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `MEM (Var v) (MAP (phi_cell_value T) cells_end)` by metis_tac[] >>
      `LIST_ELEM_COUNT (Var v) (MAP (phi_cell_value T) cells_end) <= 1` by metis_tac[] >>
      gvs[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM] >>
      qpat_x_assum `!v'. LIST_ELEM_COUNT (Var v') _ <= 1`
        (qspec_then `v` mp_tac) >>
      qpat_x_assum `!v'. LIST_ELEM_COUNT v' _ > 0 ==> _`
        (qspec_then `v` mp_tac) >> simp[] >> decide_tac) >>
  rpt gen_tac >> strip_tac >>
  `~MEM (Var v) (MAP (phi_cell_value T) cells_end)` by metis_tac[] >>
  `MEM (Var v) (MAP (phi_cell_value T) cells)` by
    (asm_rewrite_tac[] >> simp[MEM_MAP]) >>
  `LIST_ELEM_COUNT (Var v) (MAP (phi_cell_value T) cells) > 0` by
    metis_tac[rich_listTheory.LIST_ELEM_COUNT_MEM] >>
  `LIST_ELEM_COUNT (Var v) prefixP = 0 /\ Var v NOTIN FDOM ps.ps_spilled` by
    (qpat_x_assum `LIST_ELEM_COUNT _ _ + _ <= 1` mp_tac >>
     qpat_x_assum `LIST_ELEM_COUNT _ _ > 0` mp_tac >>
     asm_rewrite_tac[] >> simp[rich_listTheory.LIST_ELEM_COUNT_THM] >>
     Cases_on `Var v IN FDOM ps.ps_spilled` >> simp[] >> decide_tac) >>
  simp[MEM_APPEND] >>
  qpat_x_assum `LIST_ELEM_COUNT _ prefixP = 0` mp_tac >>
  simp[GSYM rich_listTheory.LIST_ELEM_COUNT_MEM]
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


Theorem analyzed_phi_endpoint_filter_projection:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
  phi_block_ready (liveness_analyze fn) bb /\
  phi_origin_classes (native_phi_class p (collect_phis bb.bb_instructions)) cells ==>
  FILTER (\op. MEM op (MAP Var (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions))))) (MAP (phi_cell_value T) cells) =
  FILTER (\op. MEM op (MAP Var (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions))))) (MAP (phi_cell_value F) cells)
Proof
  strip_tac >> irule phi_origin_classes_filter_projection >>
  goal_assum (drule_at Any) >>
  simp[] >> metis_tac[analyzed_native_phi_endpoint_class_dead]
QED

Theorem analyzed_phi_endpoint_mark_projection:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
  phi_block_ready (liveness_analyze fn) bb /\
  phi_origin_classes (native_phi_class p (collect_phis bb.bb_instructions)) cells ==>
  MAP (\op. if MEM op (MAP Var (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions)))) then op else dead_stack_marker)
    (MAP (phi_cell_value T) cells) =
  MAP (\op. if MEM op (MAP Var (live_vars_at (liveness_analyze fn) lbl
      (LENGTH (collect_phis bb.bb_instructions)))) then op else dead_stack_marker)
    (MAP (phi_cell_value F) cells)
Proof
  strip_tac >> ho_match_mp_tac phi_origin_classes_mark_projection >>
  goal_assum (drule_at Any) >>
  simp[] >> metis_tac[analyzed_native_phi_endpoint_class_dead]
QED

Theorem successful_join_edges_phi_common_suffix_rebased:
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
  ?prefixP prefixQ suffix ops al.
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) rsP =
      (ops, rsP with <|ps_stack := prefixP ++ suffix; ps_alloc := al|>) /\
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) rsQ =
      (ops, rsQ with <|ps_stack := prefixQ ++ suffix; ps_alloc := al|>) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
        (LENGTH (collect_phis sb.bb_instructions))) ==> MEM (Var v) suffix) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
        (LENGTH (collect_phis sb.bb_instructions))) ==> LIST_ELEM_COUNT (Var v) suffix = 1)
Proof
  rpt gen_tac >> strip_tac >>
  `?cells prefixP prefixQ.
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
      (input_vars_from p sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))` by
    (irule successful_join_edges_native_cells >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `!v i. MEM v (live_vars_at (liveness_analyze fn) succ 0) /\
    FLOOKUP (FST (build_phi_maps p (collect_phis sb.bb_instructions))) v = SOME i ==>
    IS_SOME (FLOOKUP (SND (build_phi_maps p (collect_phis sb.bb_instructions))) i) /\
    IS_SOME (FLOOKUP (SND (build_phi_maps q (collect_phis sb.bb_instructions))) i)` by
    metis_tac[] >>
  `rsP.ps_stack = prefixP ++ MAP (phi_cell_value T) cells /\
   rsQ.ps_stack = prefixQ ++ MAP (phi_cell_value F) cells` by simp[] >>
  drule_all analyzed_native_slot_state_replay >>
  disch_then (qspec_then `halting` strip_assume_tac) >>
  qexistsl_tac [`prefixP`, `prefixQ`, `suffix`, `ops`, `al`] >> simp[]
QED

(* The original execution-state interface is a specialization of rebasing. *)
Theorem successful_join_edges_phi_common_suffix:
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
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn qb psQ0 = SOME (opsQ, psQ) /\
  psP.ps_alloc = psQ.ps_alloc ==>
  ?prefixP prefixQ suffix ops al.
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) psP =
      (ops, psP with <|ps_stack := prefixP ++ suffix; ps_alloc := al|>) /\
    phi_schedule_run
      (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), halting))
        (collect_phis sb.bb_instructions)) psQ =
      (ops, psQ with <|ps_stack := prefixQ ++ suffix; ps_alloc := al|>) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
        (LENGTH (collect_phis sb.bb_instructions))) ==> MEM (Var v) suffix) /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) succ
        (LENGTH (collect_phis sb.bb_instructions))) ==> LIST_ELEM_COUNT (Var v) suffix = 1)
Proof
  rpt strip_tac >> irule successful_join_edges_phi_common_suffix_rebased >>
  rpt (goal_assum (drule_at Any)) >> simp[] >> metis_tac[]
QED

Theorem generate_block_insts_plan_phi_schedule:
  !phis rest lv dfg cfg fn lbl halting np block_len i ps phi_ops ps_phi.
  EVERY (\inst. inst.inst_opcode = PHI) phis /\ rest <> [] /\
  phi_schedule_run
    (MAPi (\j inst. (inst, live_vars_at lv lbl (i + j + np + 1), halting)) phis)
    ps = (phi_ops, ps_phi) ==>
  generate_block_insts_plan lv dfg cfg fn lbl halting np block_len i (phis ++ rest) ps =
  case generate_block_insts_plan lv dfg cfg fn lbl halting np block_len
      (i + LENGTH phis) rest ps_phi of
    NONE => NONE
  | SOME (tail_ops, out) => SOME (phi_ops ++ tail_ops, out)
Proof
  Induct_on `phis`
  >- (simp[phi_schedule_run_def] >> rpt strip_tac >> gvs[] >>
      Cases_on `generate_block_insts_plan lv dfg cfg fn lbl halting np block_len i rest ps` >> simp[] >>
      PairCases_on `x` >> simp[]) >>
  rpt gen_tac >> simp[] >> strip_tac >>
  gvs[phi_schedule_run_def, combinTheory.o_DEF, arithmeticTheory.ADD_CLAUSES] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[Once generate_block_insts_plan_def, generate_inst_plan_def,
       is_pre_codegen_opcode_def] >>
  simp[is_unlowered_fmp_opcode_def, is_unlowered_internal_call_opcode_def] >>
  simp[venomInstTheory.is_raw_fmp_opcode_def] >>
  `generate_block_insts_plan lv dfg cfg fn lbl halting np block_len (i + 1) (phis ++ rest) ps1 =
   case generate_block_insts_plan lv dfg cfg fn lbl halting np block_len
       ((i + 1) + LENGTH phis) rest ps2 of
     NONE => NONE
   | SOME (tail_ops, out) => SOME (rest' ++ tail_ops, out)` by
    (first_x_assum irule >> simp[] >>
     `MAPi (\x inst. (inst, live_vars_at lv lbl (SUC (i + (np + (x + 1)))), halting)) phis =
      MAPi (\j inst. (inst, live_vars_at lv lbl (i + (j + (np + 2))), halting)) phis` by
       (AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM] >>
        gen_tac >> AP_TERM_TAC >> decide_tac) >>
     metis_tac[]) >>
  `i + 1 + LENGTH phis = SUC (i + LENGTH phis)` by decide_tac >>
  pure_asm_rewrite_tac[] >>
  Cases_on `generate_block_insts_plan lv dfg cfg fn lbl halting np block_len
    (SUC (i + LENGTH phis)) rest ps2` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

Theorem ready_phi_block_suffix:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  collect_phis bb.bb_instructions <> [] ==>
  get_params bb.bb_instructions = [] /\
  non_param_insts bb = bb.bb_instructions /\
  ?rest. rest <> [] /\ bb.bb_instructions = collect_phis bb.bb_instructions ++ rest
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM, venomExecPropsTheory.lookup_block_label] >>
  `get_params bb.bb_instructions = []` by
    (Cases_on `bb.bb_instructions` >>
     gvs[livenessDefsTheory.collect_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >>
     gvs[get_params_def, is_param_opcode_def]) >>
  `non_param_insts bb = bb.bb_instructions` by
    metis_tac[ready_block_parameter_suffix, APPEND] >>
  simp[] >>
  qspec_then `bb.bb_instructions` strip_assume_tac collect_phis_prefix >>
  qexists_tac `rest` >> simp[] >>
  strip_tac >> gvs[] >>
  `bb_well_formed bb` by
    (gvs[codegen_ready_fn_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `MEM (LAST bb.bb_instructions) (collect_phis bb.bb_instructions)` by
    (qpat_x_assum `bb.bb_instructions = _` (fn th => rewrite_tac[GSYM th]) >>
     gvs[bb_well_formed_def] >> simp[rich_listTheory.MEM_LAST_NOT_NIL]) >>
  drule livenessTransferProofsTheory.collect_phis_mem >> strip_tac >>
  gvs[bb_well_formed_def, is_terminator_def]
QED

Theorem ready_nonentry_block_suffix:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  fn_entry_label fn <> SOME lbl ==>
  get_params bb.bb_instructions = [] /\
  non_param_insts bb = bb.bb_instructions /\
  ?rest. rest <> [] /\ bb.bb_instructions = collect_phis bb.bb_instructions ++ rest
Proof
  strip_tac >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  Cases_on `collect_phis bb.bb_instructions = []`
  >- (`bb <> HD fn.fn_blocks` by
        (Cases_on `fn.fn_blocks` >>
         gvs[fn_entry_label_def, entry_block_def, venomInstTheory.lookup_block_def,
           listTheory.FIND_thm] >> metis_tac[]) >>
      `canonical_param_prefix fn` by gvs[codegen_ready_fn_def] >>
      drule_all nonentry_block_no_params >> strip_tac >> simp[] >>
      `bb_well_formed bb` by
        (gvs[codegen_ready_fn_def, wf_function_def, EVERY_MEM] >>
         metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
      gvs[bb_well_formed_def]) >>
  metis_tac[ready_phi_block_suffix]
QED

Theorem generate_join_block_plan_phi_schedule:
  codegen_ready_fn fn /\ lookup_block lbl fn.fn_blocks = SOME bb /\
  fn_entry_label fn <> SOME lbl /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) lbl) /\
  phi_schedule_run
    (MAPi (\j inst. (inst, live_vars_at (liveness_analyze fn) lbl (SUC j),
      bb_is_halting bb)) (collect_phis bb.bb_instructions)) ps = (phi_ops, ps_phi) ==>
  get_params bb.bb_instructions = [] /\
  ?rest. rest <> [] /\
    bb.bb_instructions = collect_phis bb.bb_instructions ++ rest /\
    generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb ps =
    case generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
        (bb_is_halting bb) 0 (LENGTH bb.bb_instructions)
        (LENGTH (collect_phis bb.bb_instructions)) rest ps_phi of
      NONE => NONE
    | SOME (tail_ops, out) =>
        if revert_block_spills bb (phi_ops ++ tail_ops) then NONE
        else SOME ([SOLabel lbl] ++ phi_ops ++ tail_ops, out)
Proof
  rpt strip_tac >>
  drule_all ready_nonentry_block_suffix >> strip_tac >> simp[] >>
  qexists_tac `rest` >> simp[] >>
  `bb.bb_label = lbl` by metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `bb <> HD fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[fn_entry_label_def, entry_block_def, venomInstTheory.lookup_block_def,
       listTheory.FIND_thm] >> metis_tac[]) >>
  `LENGTH (cfg_preds_of (cfg_analyze fn) lbl) <> 1` by decide_tac >>
  `EVERY (\inst. inst.inst_opcode = PHI) (collect_phis bb.bb_instructions)` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     drule livenessTransferProofsTheory.collect_phis_mem >> simp[]) >>
  `generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) 0 (LENGTH bb.bb_instructions) 0
      (collect_phis bb.bb_instructions ++ rest) ps =
   case generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
      (bb_is_halting bb) 0 (LENGTH bb.bb_instructions)
      (0 + LENGTH (collect_phis bb.bb_instructions)) rest ps_phi of
     NONE => NONE
   | SOME (tail_ops, out) => SOME (phi_ops ++ tail_ops, out)` by
    (irule generate_block_insts_plan_phi_schedule >>
     fs[arithmeticTheory.ADD1]) >>
  qpat_x_assum `bb.bb_instructions = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  simp[generate_block_plan_def] >>
  Cases_on `generate_block_insts_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn lbl
    (bb_is_halting bb) 0 (LENGTH bb.bb_instructions)
    (LENGTH (collect_phis bb.bb_instructions)) rest ps_phi` >> simp[] >>
  PairCases_on `x` >> simp[]
QED


Theory fnLineageInvJoinContract
Ancestors fnLineageInvActualSchedule fnLineageInvSetupSuffix
  fnPlanLineagePhiSchedule fnPlanLineageInventory stackPlanGen list rich_list
  fnLineageInvLivenessDistinct fnPlanLineageEdge fnPlanLineageLiveness
  fnPlanLineagePhiClasses fnPlanLineagePhiMaps fnPlanPrefix venomExecProps

(* A consumer-side contract: the raw replay producer must supply the literal
   marker prefixes, not merely an arbitrary common suffix.  Spill maps are
   preserved separately; this statement does not invent map equality. *)
Theorem actual_phi_prefix_common_core:
 !k insts lv dfg cfg fn lbl halt np bl i ps pops pe.
 generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k insts ps = SOME (pops,pe) ==>
 !qs qops qe.
 generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k insts qs = SOME (qops,qe) ==>
 !m n suffix ops al u v pc qc.
 k <= LENGTH insts /\ EVERY (\inst. inst.inst_opcode = PHI) (TAKE k insts) /\
 (k < LENGTH insts \/ bl = i + np + k) /\
 phi_schedule_run
   (MAPi (\j inst. (inst, live_vars_at lv lbl (i + np + SUC j), halt))
     (TAKE k insts)) ps =
   (ops, ps with <|ps_stack := REPLICATE m dead_stack_marker ++ suffix; ps_alloc := al|>) /\
 phi_schedule_run
   (MAPi (\j inst. (inst, live_vars_at lv lbl (i + np + SUC j), halt))
     (TAKE k insts)) qs =
   (ops, qs with <|ps_stack := REPLICATE n dead_stack_marker ++ suffix; ps_alloc := al|>) /\
 lineage_core u pc pe /\ EVERY is_var_operand pc /\
 lineage_core v qc qe /\ EVERY is_var_operand qc ==>
 pops = qops /\ pc = qc /\ pe.ps_alloc = qe.ps_alloc /\
 pe.ps_spilled = ps.ps_spilled /\ qe.ps_spilled = qs.ps_spilled /\
 pe.ps_cleanup_height = ps.ps_cleanup_height /\
 qe.ps_cleanup_height = qs.ps_cleanup_height /\
 pe.ps_cleanup_promised = ps.ps_cleanup_promised /\
 qe.ps_cleanup_promised = qs.ps_cleanup_promised /\
 pe.ps_label_counter = ps.ps_label_counter /\ qe.ps_label_counter = qs.ps_label_counter /\
 pe.ps_cleanup_growth = ps.ps_cleanup_growth /\ qe.ps_cleanup_growth = qs.ps_cleanup_growth
Proof
 rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
 rpt gen_tac >> strip_tac >>
 gvs[actual_phi_prefix_run] >>
 qpat_x_assum `lineage_core u pc _` mp_tac >>
 qpat_x_assum `lineage_core v qc _` mp_tac >>
 simp[lineage_core_def] >> rpt strip_tac >>
 `FILTER (\op. op <> dead_stack_marker) pc = pc /\
  FILTER (\op. op <> dead_stack_marker) qc = qc` by
   (simp[FILTER_EQ_ID, EVERY_MEM] >>
    gvs[EVERY_MEM, stackPlanTypesTheory.is_var_operand_def,
        stackPlanGenTheory.dead_stack_marker_def] >>
    metis_tac[stackPlanTypesTheory.is_var_operand_def]) >>
 qpat_x_assum `_ = REPLICATE u dead_stack_marker ++ pc`
   (mp_tac o Q.AP_TERM `FILTER (\op. op <> dead_stack_marker)`) >>
 qpat_x_assum `_ = REPLICATE v dead_stack_marker ++ qc`
   (mp_tac o Q.AP_TERM `FILTER (\op. op <> dead_stack_marker)`) >>
 `!r. FILTER (\op. op <> dead_stack_marker) (REPLICATE r dead_stack_marker) = []` by
   simp[FILTER_EQ_NIL, EVERY_MEM, MEM_REPLICATE] >>
 simp[FILTER_APPEND]
QED


(* Successful exact join edges expose their original marker prefix, including
   the zero-PHI case. *)
Theorem analyzed_join_edge_marker_prefix:
 !fn pred succ pb sb dfg ps0 ops ps.
 codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
 lookup_block pred fn.fn_blocks = SOME pb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps0 =
   SOME (ops,ps) /\
 lineage_inventory
   (set (MAP Var (live_vars_at (liveness_analyze fn) pred
      (LENGTH pb.bb_instructions)))) ps ==>
 ps.ps_spilled = FEMPTY /\
 ?m. ps.ps_stack = REPLICATE m dead_stack_marker ++
   MAP Var (input_vars_from pred sb.bb_instructions
     (live_vars_at (liveness_analyze fn) succ 0))
Proof
 rpt gen_tac >> strip_tac >>
 `sb.bb_label = succ` by metis_tac[lookup_block_label] >>
 `lookup_block sb.bb_label fn.fn_blocks = SOME sb /\
  MEM sb.bb_label (cfg_succs_of (cfg_analyze fn) pred) /\
  LENGTH (cfg_preds_of (cfg_analyze fn) sb.bb_label) <> 1` by simp[] >>
 drule_all join_predecessor_jmp_shape >> strip_tac >>
 drule_all join_predecessor_single_successor >> strip_tac >>
 `set (live_vars_at (liveness_analyze fn) pred (LENGTH pb.bb_instructions)) =
  set (input_vars_from pred sb.bb_instructions
    (live_vars_at (liveness_analyze fn) succ 0))` by
   (irule analyzed_live_out_jmp >> simp[] >> metis_tac[]) >>
 `ALL_DISTINCT (input_vars_from pred sb.bb_instructions
    (live_vars_at (liveness_analyze fn) succ 0))` by
   (irule input_vars_from_distinct >> conj_tac
    >- (irule analyzed_live_vars_distinct >> simp[]) >>
    irule ready_block_phi_uses_disjoint >>
    metis_tac[lookup_block_MEM]) >>
 drule_all generate_block_plan_join_edge_suffix >> strip_tac >>
 irule lineage_inventory_target_suffix >>
 simp[MEM_MAP, dead_stack_marker_def] >>
 conj_tac >- (irule ALL_DISTINCT_MAP_INJ >> simp[]) >>
 gvs[LIST_TO_SET_MAP] >> metis_tac[]
QED

Theorem analyzed_join_pair_actual_phi_common_core:
 !fn entry p pb q qb succ sb dfg psP0 opsP psP psQ0 opsQ psQ
   d hp bp hq bq s t k bl insts pops qops pe qe u pc v qc.
 codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\
 fn_reachable fn succ /\ succ <> entry /\ MEM succ (cfg_analyze fn).cfg_dfs_pre /\
 cfg_reachable_of (cfg_analyze fn) p /\ cfg_reachable_of (cfg_analyze fn) q /\
 lookup_block p fn.fn_blocks = SOME pb /\ lookup_block q fn.fn_blocks = SOME qb /\
 lookup_block succ fn.fn_blocks = SOME sb /\
 MEM succ (cfg_succs_of (cfg_analyze fn) p) /\
 MEM succ (cfg_succs_of (cfg_analyze fn) q) /\
 1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb psP0 = SOME (opsP,psP) /\
 generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn qb psQ0 = SOME (opsQ,psQ) /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) p
   (LENGTH pb.bb_instructions)))) psP /\
 lineage_inventory (set (MAP Var (live_vars_at (liveness_analyze fn) q
   (LENGTH qb.bb_instructions)))) psQ /\
 s = ((d with <|ps_stack := psP.ps_stack; ps_spilled := psP.ps_spilled|>)
   with <|ps_cleanup_height := hp; ps_cleanup_promised := bp|>) /\
 t = ((d with <|ps_stack := psQ.ps_stack; ps_spilled := psQ.ps_spilled|>)
   with <|ps_cleanup_height := hq; ps_cleanup_promised := bq|>) /\
 k = LENGTH (collect_phis sb.bb_instructions) /\ k <= LENGTH insts /\
 TAKE k insts = collect_phis sb.bb_instructions /\ (k < LENGTH insts \/ bl = k) /\
 generate_block_insts_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ F 0 bl 0 k insts s = SOME (pops,pe) /\
 generate_block_insts_prefix (liveness_analyze fn) dfg (cfg_analyze fn) fn succ F 0 bl 0 k insts t = SOME (qops,qe) /\
 lineage_core u pc pe /\ EVERY is_var_operand pc /\
 lineage_core v qc qe /\ EVERY is_var_operand qc ==>
 pops = qops /\ pc = qc /\ pe.ps_alloc = qe.ps_alloc /\
 pe.ps_spilled = FEMPTY /\ qe.ps_spilled = FEMPTY /\
 pe.ps_label_counter = qe.ps_label_counter /\
 pe.ps_cleanup_growth = qe.ps_cleanup_growth /\
 pe.ps_cleanup_height = hp /\ qe.ps_cleanup_height = hq /\
 pe.ps_cleanup_promised = bp /\ qe.ps_cleanup_promised = bq
Proof
 rpt gen_tac >> strip_tac >>
 `psP.ps_spilled = FEMPTY /\
  ?m. psP.ps_stack = REPLICATE m dead_stack_marker ++
    MAP Var (input_vars_from p sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))` by
   (irule analyzed_join_edge_marker_prefix >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
 `psQ.ps_spilled = FEMPTY /\
  ?n. psQ.ps_stack = REPLICATE n dead_stack_marker ++
    MAP Var (input_vars_from q sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))` by
   (irule analyzed_join_edge_marker_prefix >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
 `?suffix raw al.
  phi_schedule_run (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), F))
    (collect_phis sb.bb_instructions)) s =
    (raw, s with <|ps_stack := REPLICATE m dead_stack_marker ++ suffix; ps_alloc := al|>) /\
  phi_schedule_run (MAPi (\i inst. (inst, live_vars_at (liveness_analyze fn) succ (SUC i), F))
    (collect_phis sb.bb_instructions)) t =
    (raw, t with <|ps_stack := REPLICATE n dead_stack_marker ++ suffix; ps_alloc := al|>)` by
  (Cases_on `k = 0`
   >- (gvs[] >> qexistsl_tac [`MAP Var (live_vars_at (liveness_analyze fn) succ 0)`, `[]`, `d.ps_alloc`] >>
       simp[fnPlanLineagePhiTemporalTheory.phi_schedule_run_def, livenessDefsTheory.input_vars_from_def,
         stackPlanTypesTheory.plan_state_component_equality]) >>
   `~NULL (collect_phis sb.bb_instructions)` by (Cases_on `collect_phis sb.bb_instructions` >> gvs[]) >>
   mp_tac (SPEC_ALL fnPlanLineageJoinEntryTheory.successful_join_edges_native_cells) >>
   (impl_tac >- simp[]) >> strip_tac >>
   `MAP (phi_cell_value F) cells = MAP Var
     (input_vars_from q sb.bb_instructions (live_vars_at (liveness_analyze fn) succ 0))` by
    (qpat_assum `cells = _` (fn th => rewrite_tac[th]) >>
     irule fnPlanLineagePhiRealizationTheory.input_vars_from_cells_projection >>
     simp[pairTheory.PAIR_FST_SND_EQ] >> metis_tac[build_phi_maps_source_independent]) >>
   `prefixP = REPLICATE m dead_stack_marker /\ prefixQ = REPLICATE n dead_stack_marker` by
     metis_tac[APPEND_11] >>
   irule analyzed_native_slot_state_replay >>
   simp[] >> qexistsl_tac [`live_vars_at (liveness_analyze fn) succ 0`, `p`, `q`] >>
   simp[] >> metis_tac[]) >>
 `EVERY (\inst. inst.inst_opcode = PHI) (TAKE k insts)` by
   (simp[EVERY_MEM] >> metis_tac[livenessProofsTheory.collect_phis_mem]) >>
 qpat_x_assum `TAKE k insts = _`
   (fn th => rule_assum_tac (REWRITE_RULE [GSYM th])) >>
 qpat_assum `generate_block_insts_prefix _ _ _ _ _ _ _ _ _ _ _ s = _`
   (mp_then Any mp_tac actual_phi_prefix_common_core) >>
 disch_then (qspecl_then [`t`, `qops`, `qe`] mp_tac) >>
 simp[IgnAsm `s = _`, IgnAsm `t = _`] >>
 disch_then (qspecl_then [`m`, `n`, `suffix`, `al`] mp_tac) >>
 simp[IgnAsm `s = _`, IgnAsm `t = _`] >>
 disch_tac >> gvs[] >> metis_tac[]
QED

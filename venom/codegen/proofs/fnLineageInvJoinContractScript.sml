Theory fnLineageInvJoinContract
Ancestors fnLineageInvActualSchedule fnLineageInvSetupSuffix
  fnPlanLineagePhiSchedule fnPlanLineageInventory stackPlanGen list rich_list
  fnLineageInvLivenessDistinct fnPlanLineageEdge fnPlanLineageLiveness
  fnPlanLineagePhiClasses fnPlanLineagePhiMaps fnPlanPrefix venomExecProps

(* A consumer-side contract: the raw replay producer must supply the literal
   marker prefixes, not merely an arbitrary common suffix.  Spill maps are
   preserved separately; this statement does not invent map equality. *)
Theorem actual_phi_prefix_common_core:
 !k insts lv dfg cfg fn lbl halt np bl i ps qs pops qops pe qe
   m n suffix ops al u v pc qc.
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
 generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k insts ps = SOME (pops,pe) /\
 generate_block_insts_prefix lv dfg cfg fn lbl halt np bl i k insts qs = SOME (qops,qe) /\
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

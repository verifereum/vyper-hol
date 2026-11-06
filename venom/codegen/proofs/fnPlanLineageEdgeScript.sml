Theory fnPlanLineageEdge
Ancestors
  fnPlanPrefix fnPlanLineageSuffix fnPlanLineageInventory fnPlanLineageLiveness
  stackPlanGen venomInst venomWf venomExecProps cfgAnalysisProps list rich_list

(* stack_get_depth_is_some supplies the generic membership/search boundary. *)
Theorem generate_block_plan_jmp_target_hit:
  generate_block_plan lv dfg cfg fn pb ps = SOME (ops, ps') /\
  non_param_insts pb <> [] /\ (LAST (non_param_insts pb)).inst_opcode = JMP /\
  join_target_ops lv fn pb.bb_label (LAST (non_param_insts pb)) = SOME targets /\
  MEM op targets ==>
  ?d. stack_get_depth op ps'.ps_stack = SOME d
Proof
  rpt strip_tac >> drule_all generate_block_plan_jmp_suffix >> strip_tac >>
  `MEM op ps'.ps_stack` by simp[] >>
  fs[GSYM stack_get_depth_is_some, optionTheory.IS_SOME_EXISTS]
QED

Theorem analyzed_jmp_block_live_out_hit:
  codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pb.bb_label /\
  lookup_block pb.bb_label fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  pb.bb_instructions <> [] /\ LAST pb.bb_instructions = inst /\
  inst.inst_opcode = JMP /\ inst.inst_operands = [Label succ] /\
  non_param_insts pb <> [] /\ LAST (non_param_insts pb) = inst /\
  generate_block_plan (liveness_analyze fn) dfg cfg fn pb ps = SOME (ops, ps') /\
  MEM v (live_vars_at (liveness_analyze fn) pb.bb_label (LENGTH pb.bb_instructions)) ==>
  ?d. stack_get_depth (Var v) ps'.ps_stack = SOME d
Proof
  rpt strip_tac >> drule_all analyzed_live_out_jmp >> strip_tac >>
  irule generate_block_plan_jmp_target_hit >>
  goal_assum (drule_at Any) >>
  simp[join_target_ops_def] >>
  qpat_x_assum `set _ = set _` mp_tac >>
  simp[pred_setTheory.EXTENSION, listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem generate_block_plan_join_edge_suffix:
  codegen_ready_fn fn /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  generate_block_plan lv dfg (cfg_analyze fn) fn pb ps = SOME (ops, ps') ==>
  ?prefix. ps'.ps_stack = prefix ++
    MAP Var (input_vars_from pred sb.bb_instructions (live_vars_at lv succ 0))
Proof
  strip_tac >>
  `sb.bb_label = succ` by metis_tac[lookup_block_label] >>
  `LENGTH (cfg_preds_of (cfg_analyze fn) sb.bb_label) <> 1 /\
   lookup_block sb.bb_label fn.fn_blocks = SOME sb /\
   MEM sb.bb_label (cfg_succs_of (cfg_analyze fn) pred)` by simp[] >>
  drule_all join_predecessor_jmp_shape >> strip_tac >>
  drule_all join_predecessor_single_successor >> strip_tac >>
  drule_all non_param_insts_last_jmp >> strip_tac >>
  `pb.bb_label = pred` by metis_tac[lookup_block_label] >>
  `join_target_ops lv fn pb.bb_label (LAST (non_param_insts pb)) =
   SOME (MAP Var (input_vars_from pred sb.bb_instructions (live_vars_at lv succ 0)))` by
    simp[join_target_ops_def] >>
  `(LAST (non_param_insts pb)).inst_opcode = JMP` by simp[] >>
  drule_all generate_block_plan_jmp_suffix >> simp[]
QED

Theorem analyzed_terminal_jmp_spilled_empty:
  !fn pred succ pred_bb succ_bb inst dfg cfg halt term ps ops ps'.
    codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
    lookup_block pred fn.fn_blocks = SOME pred_bb /\
    lookup_block succ fn.fn_blocks = SOME succ_bb /\
    pred_bb.bb_instructions <> [] /\ LAST pred_bb.bb_instructions = inst /\
    inst.inst_opcode = JMP /\ inst.inst_operands = [Label succ] /\
    inst.inst_outputs = [] /\
    generate_inst_plan (liveness_analyze fn) dfg cfg fn inst
      (live_vars_at (liveness_analyze fn) pred (LENGTH pred_bb.bb_instructions))
      halt term pred ps = SOME (ops,ps') ==>
    ps'.ps_spilled = FEMPTY
Proof
  rpt gen_tac >> strip_tac >>
  drule_all analyzed_live_out_jmp >> strip_tac >>
  irule phi_jmp_plan_spills_empty >>
  goal_assum (drule_at Any) >> simp[join_target_ops_def] >>
  qpat_x_assum `set _ = set _` mp_tac >>
  simp[pred_setTheory.EXTENSION, pred_setTheory.SUBSET_DEF, MEM_MAP] >>
  metis_tac[]
QED

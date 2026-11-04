Theory fnPlanLineageEdge
Ancestors
  fnPlanLineageSuffix fnPlanLineageInventory fnPlanLineageLiveness
  stackPlanGen venomInst

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

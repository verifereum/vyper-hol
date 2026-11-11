Theory fnPlanLineageEdge
Ancestors cfgCorrectnessProof
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

Theorem ready_join_edge_terminator:
  codegen_ready_fn fn /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) ==>
  pb.bb_instructions <> [] /\
  (LAST pb.bb_instructions).inst_opcode = JMP /\
  (LAST pb.bb_instructions).inst_operands = [Label succ]
Proof
  strip_tac >>
  `MEM pb fn.fn_blocks /\ pb.bb_label = pred /\
   MEM sb fn.fn_blocks /\ sb.bb_label = succ` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `MEM pred (cfg_preds_of (cfg_analyze fn) succ)` by
    metis_tac[cfg_edge_symmetry_uncond] >>
  `block_entries_ready (cfg_analyze fn) fn /\ wf_function fn /\ fn_inst_wf fn` by
    gvs[codegen_ready_fn_def] >>
  `~NULL pb.bb_instructions /\ (LAST pb.bb_instructions).inst_opcode = JMP` by
    (gvs[block_entries_ready_def, EVERY_MEM] >>
     qpat_x_assum `!bb. MEM bb fn.fn_blocks ==> _`
       (qspec_then `sb` mp_tac) >> simp[] >> strip_tac >>
     first_x_assum (qspec_then `pb.bb_label` mp_tac) >> simp[]) >>
  `pb.bb_instructions <> []` by gvs[NULL_EQ] >>
  `MEM (LAST pb.bb_instructions) pb.bb_instructions` by metis_tac[LAST_MEM] >>
  `inst_wf (LAST pb.bb_instructions)` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >>
     first_x_assum irule >> qexists_tac `pb` >> simp[LAST_MEM, NULL_EQ]) >>
  `?target. (LAST pb.bb_instructions).inst_operands = [Label target]` by
    gvs[inst_wf_def] >>
  `cfg_succs_of (cfg_analyze fn) pred = bb_succs pb` by
    metis_tac[cfg_analyze_preserves_bb_succs] >>
  gvs[NULL_EQ, bb_succs_def, get_successors_def, is_terminator_def,
      venomStateTheory.get_label_def, nub_def, AllCaseEqs()] >>
  qpat_x_assum `[_] = cfg_succs_of _ _` (assume_tac o SYM) >> gvs[]
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

Theorem analyzed_join_edge_spilled_empty:
  codegen_ready_fn fn /\ cfg_reachable_of (cfg_analyze fn) pred /\
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME sb /\
  MEM succ (cfg_succs_of (cfg_analyze fn) pred) /\
  1 < LENGTH (cfg_preds_of (cfg_analyze fn) succ) /\
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn pb ps =
    SOME (ops,ps') ==>
  ps'.ps_spilled = FEMPTY
Proof
  strip_tac >> drule_all ready_join_edge_terminator >> strip_tac >>
  drule_all non_param_insts_last_jmp >> strip_tac >>
  `pb.bb_label = pred` by metis_tac[lookup_block_label] >>
  `inst_wf (LAST pb.bb_instructions)` by
    ( `fn_inst_wf fn` by gvs[codegen_ready_fn_def] >>
      gvs[fn_inst_wf_def, EVERY_MEM] >> first_x_assum irule >>
      qexists_tac `pb` >> simp[LAST_MEM, NULL_EQ] >>
      metis_tac[lookup_block_MEM]) >>
  `(LAST pb.bb_instructions).inst_outputs = []` by gvs[inst_wf_def] >>
  qpat_x_assum `generate_block_plan _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_block_plan_def] >> rpt (pairarg_tac >> gvs[]) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all generate_block_insts_plan_final_call >> strip_tac >>
  gvs[] >>
  drule_at (Pos last) analyzed_terminal_jmp_spilled_empty >>
  simp[] >> disch_then irule >> goal_assum (drule_at Any) >> simp[]
QED

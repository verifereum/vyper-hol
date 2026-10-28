(* Discharge the real block-prefix pairs before its instruction continuation. *)
Theory stackPlanBlockCases
Ancestors stackPlanGen

Definition planner_block_entry_def:
  planner_block_entry liveness func bb ps =
    if bb = HD func.fn_blocks then prepare_params_plan liveness func ps
    else ([] : stack_op list,ps)
End

Definition planner_block_cleanup_def:
  planner_block_cleanup liveness cfg func bb ps =
    if LENGTH (cfg_preds_of cfg bb.bb_label) = 1 then
      clean_stack_plan liveness cfg func bb ps
    else ([] : stack_op list,ps)
End

Theorem generate_block_plan_parts:
  planner_block_entry liveness func bb ps = (param_ops,ps1) /\
  planner_block_cleanup liveness cfg func bb ps1 = (clean_ops,ps2) ==>
  generate_block_plan liveness dfg cfg func bb ps =
    case generate_block_insts_plan liveness dfg cfg func bb.bb_label
        (bb_is_halting bb) (LENGTH (get_params bb.bb_instructions))
        (LENGTH bb.bb_instructions) 0 (non_param_insts bb) ps2 of
      NONE => NONE
    | SOME (inst_ops,ps3) =>
        SOME ([SOLabel bb.bb_label] ++ param_ops ++ clean_ops ++ inst_ops,ps3)
Proof
  strip_tac >> fs[planner_block_entry_def,planner_block_cleanup_def] >>
  simp[generate_block_plan_def,LET_THM]
QED

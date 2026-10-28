(* Eliminate instruction-input lets before instantiating compiler payloads. *)
Theory stackPlanInstructionCases
Ancestors stackPlanGen

Theorem generate_block_insts_plan_cons:
  generate_block_insts_plan liveness dfg cfg func bb_label is_halting
    n_params block_len i (inst::rest) ps =
  case generate_inst_plan liveness dfg cfg func inst
      (if rest = [] then live_vars_at liveness bb_label block_len
       else live_vars_at liveness bb_label (i + n_params + 1))
      is_halting
      (case rest of [] => F | next_i::_ => is_terminator next_i.inst_opcode)
      bb_label ps of
    NONE => NONE
  | SOME (step_ops,ps1) =>
      case generate_block_insts_plan liveness dfg cfg func bb_label is_halting
          n_params block_len (i + 1) rest ps1 of
        NONE => NONE
      | SOME (rest_ops,ps2) => SOME (step_ops ++ rest_ops,ps2)
Proof
  simp[Once generate_block_insts_plan_def, LET_THM]
QED

Theorem generate_block_insts_plan_some:
  generate_inst_plan liveness dfg cfg func inst
      (if rest = [] then live_vars_at liveness bb_label block_len
       else live_vars_at liveness bb_label (i + n_params + 1))
      is_halting
      (case rest of [] => F | next_i::_ => is_terminator next_i.inst_opcode)
      bb_label ps = SOME (step_ops,ps1) ==>
  generate_block_insts_plan liveness dfg cfg func bb_label is_halting
    n_params block_len i (inst::rest) ps =
  case generate_block_insts_plan liveness dfg cfg func bb_label is_halting
      n_params block_len (i + 1) rest ps1 of
    NONE => NONE
  | SOME (rest_ops,ps2) => SOME (step_ops ++ rest_ops,ps2)
Proof
  strip_tac >> simp[generate_block_insts_plan_cons]
QED

Theorem generate_block_insts_plan_none:
  generate_inst_plan liveness dfg cfg func inst
      (if rest = [] then live_vars_at liveness bb_label block_len
       else live_vars_at liveness bb_label (i + n_params + 1))
      is_halting
      (case rest of [] => F | next_i::_ => is_terminator next_i.inst_opcode)
      bb_label ps = NONE ==>
  generate_block_insts_plan liveness dfg cfg func bb_label is_halting
    n_params block_len i (inst::rest) ps = NONE
Proof
  strip_tac >> simp[generate_block_insts_plan_cons]
QED

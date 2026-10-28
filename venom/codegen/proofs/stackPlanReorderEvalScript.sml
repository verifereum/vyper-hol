(* Exact planner workers with explicit equivalence and fold boundaries. *)
Theory stackPlanReorderEval
Ancestors stackPlanOps stackPlanGen
Libs pairLib

Definition planner_reorder_fold_def:
  (planner_reorder_fold dfg targets [] (ops,ps) = (ops,ps)) /\
  (planner_reorder_fold dfg targets ((idx,operand)::rest) (ops,ps) =
    let (step_ops,ps') = reorder_one dfg targets idx operand ps in
    planner_reorder_fold dfg targets rest (ops ++ step_ops,ps'))
End

Theorem planner_reorder_fold_eq:
  !items ops ps.
  planner_reorder_fold dfg targets items (ops,ps) =
    FOLDL (\(ops,ps) (idx,operand).
      let (step_ops,ps') = reorder_one dfg targets idx operand ps in
      (ops ++ step_ops,ps')) (ops,ps) items
Proof
  Induct >> simp[planner_reorder_fold_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[planner_reorder_fold_def] >> pairarg_tac >> simp[]
QED

Theorem reorder_plan_fold:
  reorder_plan dfg targets ps =
    planner_reorder_fold dfg targets (MAPi (\i operand. (i,operand)) targets)
      ([] : stack_op list,ps)
Proof
  simp[planner_reorder_fold_eq,reorder_plan_def]
QED

Theorem planner_reorder_fold_cons_result:
  !dfg targets idx operand rest ops ps step_ops ps'.
  reorder_one dfg targets idx operand ps = (step_ops,ps') ==>
  planner_reorder_fold dfg targets ((idx,operand)::rest) (ops,ps) =
    planner_reorder_fold dfg targets rest (ops ++ step_ops,ps')
Proof
  simp[planner_reorder_fold_def]
QED

Definition planner_reorder_one_def:
  planner_reorder_one equivalent target_ops target_idx op ps =
    let num_ops = LENGTH target_ops in
    let final_dist = num_ops - 1 - target_idx in
    (* Find an unfixed occurrence, or restore a spilled copy at unprotected TOS. *)
    let (restore_ops, ps1) =
      case stack_get_unfixed_depth op final_dist num_ops ps.ps_stack of
        SOME _ => ([] : stack_op list, ps)
      | NONE =>
          (case FLOOKUP ps.ps_spilled op of
            SOME _ => do_restore op ps
          | NONE => ([], ps)) in
    case stack_get_unfixed_depth op final_dist num_ops ps1.ps_stack of
      NONE => (restore_ops, ps1)
    | SOME dist =>
        let (reduce_ops, ps2) =
          if dist > 16
          then reduce_depth_plan (LENGTH ps1.ps_stack) target_ops op
                 final_dist num_ops ps1
          else ([] : stack_op list, ps1) in
        case stack_get_unfixed_depth op final_dist num_ops ps2.ps_stack of
          NONE => (restore_ops ++ reduce_ops, ps2)
        | SOME dist' =>
            if dist' = final_dist then
              (restore_ops ++ reduce_ops, ps2)
            else if final_dist < LENGTH ps2.ps_stack then
              let at_target = stack_peek final_dist ps2.ps_stack in
              if equivalent op at_target then
                let ps3 = ps2 with ps_stack :=
                  stack_poke final_dist op
                    (stack_poke dist' at_target ps2.ps_stack) in
                (restore_ops ++ reduce_ops, ps3)
              else
                let (swap1_ops, ps3) = do_swap dist' ps2 in
                let (swap2_ops, ps4) = do_swap final_dist ps3 in
                (restore_ops ++ reduce_ops ++ swap1_ops ++ swap2_ops, ps4)
            else
              let (swap1_ops, ps3) = do_swap dist' ps2 in
              let (swap2_ops, ps4) = do_swap final_dist ps3 in
              (restore_ops ++ reduce_ops ++ swap1_ops ++ swap2_ops, ps4)
End

Theorem reorder_one_planner:
  reorder_one dfg targets index operand ps =
    planner_reorder_one (operand_equiv dfg) targets index operand ps
Proof
  simp[reorder_one_def,planner_reorder_one_def]
QED

Definition planner_optimistic_swap_def:
  planner_optimistic_swap equivalent inst next_liveness next_is_terminator ps =
    (* Python: skip if next instruction is a basic block terminator *)
    if next_is_terminator then ([] : stack_op list, ps)
    else if inst.inst_outputs = [] then ([], ps)
    else if next_liveness = [] then ([], ps)
    else
      let next_scheduled = LAST next_liveness in
      let current_top = LAST inst.inst_outputs in
      if equivalent (Var current_top) (Var next_scheduled)
      then ([], ps)
      else
        case stack_get_depth (Var next_scheduled) ps.ps_stack of
          NONE => ([], ps)
        | SOME dist => do_swap dist ps
End

Theorem optimistic_swap_planner:
  optimistic_swap_plan dfg inst next_live next_term ps =
    planner_optimistic_swap (operand_equiv dfg) inst next_live next_term ps
Proof
  simp[optimistic_swap_plan_def,planner_optimistic_swap_def]
QED

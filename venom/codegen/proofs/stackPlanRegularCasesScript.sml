(* Exact boundaries between the original regular-instruction planning phases. *)
Theory stackPlanRegularCases
Ancestors stackPlanGen
Libs pairLib

Definition planner_regular_join_def:
  planner_regular_join liveness dfg func inst cur_bb_label ps =
    if inst.inst_opcode = JMP then
      (case inst.inst_operands of
        [Label target] =>
          let target_live = live_vars_at liveness target 0 in
          (case lookup_block target func.fn_blocks of
            NONE => ([] : stack_op list,ps)
          | SOME target_bb =>
              let target_stack = input_vars_from cur_bb_label
                target_bb.bb_instructions target_live in
              reorder_plan dfg (MAP Var target_stack) ps)
      | _ => ([],ps))
    else ([],ps)
End

Definition planner_regular_reorder_def:
  planner_regular_reorder dfg opc operands ps =
    if is_commutative opc /\ LENGTH operands >= 2 then
      let (ops_a,ps_a) = reorder_plan dfg operands ps in
      let cost_a = reorder_cost ops_a in
      let n = LENGTH operands in
      let swapped = TAKE (n - 2) operands ++
        [EL (n - 1) operands; EL (n - 2) operands] in
      let (ops_b,ps_b) = reorder_plan dfg swapped ps in
      let cost_b = reorder_cost ops_b in
      if cost_a < cost_b then (ops_a,ps_a) else (ops_b,ps_b)
    else reorder_plan dfg operands ps
End

Definition planner_regular_stack_def:
  planner_regular_stack operands outputs ps =
    FOLDL (\ps' out.
      ps' with ps_stack := stack_push (Var out) ps'.ps_stack)
      (ps with ps_stack := stack_pop (LENGTH operands) ps.ps_stack) outputs
End

Definition planner_regular_finish_def:
  planner_regular_finish dfg inst next_liveness is_halting next_is_term ps =
    if inst.inst_outputs = [] then
      ([] : stack_op list,release_dead_spills next_liveness ps)
    else
      let (pop_ops,ps8) =
        if ~is_halting then
          let dead = FILTER (\out. ~MEM out next_liveness) inst.inst_outputs in
          popmany_plan (MAP Var dead) ps
        else ([],ps) in
      let live_outs = FILTER (\out. MEM out next_liveness) inst.inst_outputs in
      let (opt_ops,ps9) =
        if live_outs = [] then ([],ps8)
        else optimistic_swap_plan dfg inst next_liveness next_is_term ps8 in
      (pop_ops ++ opt_ops,release_dead_spills next_liveness ps9)
End

Theorem generate_regular_inst_plan_parts:
  !liveness dfg cfg func inst next_liveness is_halting next_is_term label ps
    input_ops ps1 join_ops ps2 reorder_ops ps4 emit_ops ps7 post_ops ps10.
  emit_input_plan inst.inst_opcode (compute_operands inst) next_liveness ps =
    (input_ops,ps1) /\
  planner_regular_join liveness dfg func inst label ps1 = (join_ops,ps2) /\
  planner_regular_reorder dfg inst.inst_opcode (compute_operands inst) ps2 =
    (reorder_ops,ps4) /\
  generate_emit_ops inst
    (case inst.inst_opcode of LOG =>
       (case HD inst.inst_operands of Lit value => w2n value | _ => 0)
     | _ => 0)
    (planner_regular_stack (compute_operands inst) inst.inst_outputs ps4) =
    (emit_ops,ps7) /\
  planner_regular_finish dfg inst next_liveness is_halting next_is_term ps7 =
    (post_ops,ps10) ==>
  generate_regular_inst_plan liveness dfg cfg func inst next_liveness
    is_halting next_is_term label ps =
    (input_ops ++ join_ops ++ reorder_ops ++ emit_ops ++ post_ops,ps10)
Proof
  rpt gen_tac >> strip_tac >>
  fs[planner_regular_join_def,planner_regular_reorder_def,
     planner_regular_stack_def] >>
  simp[generate_regular_inst_plan_def,LET_THM] >>
  qpat_x_assum `planner_regular_finish _ _ _ _ _ _ = _` mp_tac >>
  simp[planner_regular_finish_def,LET_THM] >>
  Cases_on `inst.inst_outputs = []` >> simp[] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
QED

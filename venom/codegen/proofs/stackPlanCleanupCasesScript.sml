(* The real singleton-predecessor continuation of clean_stack_plan, factored
   at the tail-list case. All compiler payloads are schematic at this boundary.
   TOP-LEVEL: planner_cleanup_case, planner_cleanup_singleton. *)
Theory stackPlanCleanupCases
Ancestors stackPlanGen list

Definition planner_cleanup_single_def:
  planner_cleanup_single liveness cfg func bb ps pred_lbl =
    if LENGTH (cfg_succs_of cfg pred_lbl) ≤ 1 then
          ([] : stack_op list, ps)
        else
          (case lookup_block pred_lbl func.fn_blocks of
            NONE => ([], ps)
          | SOME pred_bb =>
              let inputs = input_vars_from pred_lbl
                bb.bb_instructions
                (live_vars_at liveness bb.bb_label 0) in
              let layout = live_vars_at liveness pred_lbl
                (LENGTH pred_bb.bb_instructions) in
              let to_pop = FILTER (λv. ¬ MEM v inputs) layout in
              (* Even a halting block with no live inputs must mark retained
                 physical slots dead.  Python keeps the slots but replaces
                 their logical identities before planning REVERT/RETURN. *)
              if NULL inputs ∧ cleanup_elision_safe cfg func bb then
                ([], ps with ps_stack :=
                  MAP (K dead_stack_marker) ps.ps_stack)
              else if cleanup_elision_safe cfg func bb then
                let physical = FILTER (λop.
                      IS_SOME (stack_get_depth op ps.ps_stack))
                      (MAP Var to_pop) in
                let retained = FILTER (λop.
                      below_all_live op inputs ps.ps_stack) physical in
                let to_cleanup = FILTER (λop. ¬MEM op retained) physical in
                let (ops, ps') = popmany_plan to_cleanup ps in
                (ops, ps' with ps_stack :=
                  mark_dead_stack retained ps'.ps_stack)
              else popmany_plan (MAP Var to_pop) ps)
End

Definition planner_cleanup_tail_def:
  planner_cleanup_tail liveness cfg func bb ps pred_lbl rest =
    case rest of
      [] => planner_cleanup_single liveness cfg func bb ps pred_lbl
    | _ => ([], ps)
End

Theorem planner_cleanup_singleton:
  planner_cleanup_tail liveness cfg func bb ps pred_lbl [] =
    planner_cleanup_single liveness cfg func bb ps pred_lbl
Proof
  simp[planner_cleanup_tail_def]
QED

Theorem planner_cleanup_nonempty:
  planner_cleanup_tail liveness cfg func bb ps pred_lbl (next::rest) = ([], ps)
Proof
  simp[planner_cleanup_tail_def]
QED

Theorem planner_cleanup_case:
  clean_stack_plan liveness cfg func bb ps =
    case cfg_preds_of cfg bb.bb_label of
      [] => ([], ps)
    | pred_lbl::rest => planner_cleanup_tail liveness cfg func bb ps pred_lbl rest
Proof
  Cases_on `cfg_preds_of cfg bb.bb_label` >>
  simp[clean_stack_plan_def, planner_cleanup_tail_def, planner_cleanup_single_def] >>
  rename1 `pred_lbl::rest` >> Cases_on `rest` >>
  simp[clean_stack_plan_def, planner_cleanup_tail_def, planner_cleanup_single_def]
QED

Theorem planner_cleanup_single_predecessor:
  cfg_preds_of cfg bb.bb_label = [pred_lbl] ==>
  clean_stack_plan liveness cfg func bb ps =
    planner_cleanup_single liveness cfg func bb ps pred_lbl
Proof
  simp[planner_cleanup_case, planner_cleanup_singleton]
QED

Theorem planner_cleanup_no_predecessors:
  cfg_preds_of cfg bb.bb_label = [] ==>
  clean_stack_plan liveness cfg func bb ps = ([], ps)
Proof
  strip_tac >> simp[planner_cleanup_case]
QED

Theorem planner_cleanup_many_predecessors:
  cfg_preds_of cfg bb.bb_label = first::second::rest ==>
  clean_stack_plan liveness cfg func bb ps = ([], ps)
Proof
  strip_tac >> simp[planner_cleanup_case, planner_cleanup_nonempty]
QED

(* This continuation needs only the observed lists and safety flag. *)
Definition planner_cleanup_apply_def:
  planner_cleanup_apply ps inputs layout safe =
    let to_pop = FILTER (\v. ~MEM v inputs) layout in
    if NULL inputs /\ safe then
      ([], ps with ps_stack := MAP (K dead_stack_marker) ps.ps_stack)
    else if safe then
      let physical = FILTER (\op. IS_SOME (stack_get_depth op ps.ps_stack))
                       (MAP Var to_pop) in
      let retained = FILTER (\op. below_all_live op inputs ps.ps_stack) physical in
      let to_cleanup = FILTER (\op. ~MEM op retained) physical in
      let (ops, ps') = popmany_plan to_cleanup ps in
        (ops, ps' with ps_stack := mark_dead_stack retained ps'.ps_stack)
    else popmany_plan (MAP Var to_pop) ps
End

Theorem planner_cleanup_single_skip:
  LENGTH (cfg_succs_of cfg pred_lbl) <= 1 ==>
  planner_cleanup_single liveness cfg func bb ps pred_lbl = ([], ps)
Proof
  strip_tac >> simp[planner_cleanup_single_def]
QED

Theorem planner_cleanup_single_missing:
  lookup_block pred_lbl func.fn_blocks = NONE ==>
  planner_cleanup_single liveness cfg func bb ps pred_lbl = ([], ps)
Proof
  strip_tac >> simp[planner_cleanup_single_def]
QED

Theorem planner_cleanup_single_found:
  ~(LENGTH (cfg_succs_of cfg pred_lbl) <= 1) /\
  lookup_block pred_lbl func.fn_blocks = SOME pred_bb ==>
  planner_cleanup_single liveness cfg func bb ps pred_lbl =
    planner_cleanup_apply ps
      (input_vars_from pred_lbl bb.bb_instructions
        (live_vars_at liveness bb.bb_label 0))
      (live_vars_at liveness pred_lbl (LENGTH pred_bb.bb_instructions))
      (cleanup_elision_safe cfg func bb)
Proof
  rpt strip_tac >> simp[planner_cleanup_single_def, planner_cleanup_apply_def]
QED

(* A cheap upper bound can discharge the original frame-size guard without
   constructing its quadratic duplicate-removal result. *)
Definition planner_cleanup_candidates_def:
  planner_cleanup_candidates func =
    FLAT (MAP (\bb. FLAT (MAP (\inst.
      operand_vars inst.inst_operands ++ inst.inst_outputs)
      bb.bb_instructions)) func.fn_blocks)
End

Theorem planner_nub_length_bound:
  !xs. LENGTH (nub xs) <= LENGTH xs
Proof
  Induct >> simp[nub_def] >> rw[] >> decide_tac
QED

Theorem planner_cleanup_frame_bound:
  LENGTH (planner_cleanup_candidates func) + cleanup_max_transient func <= 1024 ==>
  LENGTH (cleanup_frame_vars func) + cleanup_max_transient func <= 1024
Proof
  strip_tac >>
  qspec_then `planner_cleanup_candidates func` mp_tac planner_nub_length_bound >>
  gvs[cleanup_frame_vars_def, planner_cleanup_candidates_def] >> decide_tac
QED

Theorem planner_cleanup_safety_frame_bound:
  LENGTH (planner_cleanup_candidates func) + cleanup_max_transient func <= 1024 ==>
  cleanup_elision_safe cfg func bb =
    (~EXISTS (\inst. is_param_opcode inst.inst_opcode)
       (FLAT (MAP (\b. b.bb_instructions) func.fn_blocks)) /\
     MEM bb.bb_label (must_halt_labels cfg func))
Proof
  strip_tac >> drule planner_cleanup_frame_bound >>
  simp[cleanup_elision_safe_def]
QED


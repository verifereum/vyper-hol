Theory fnPlanLineageObservation
Ancestors
  stackPlanGen list pred_set

(* Keep unobserved cells positional: NONE is a cell, not deletion. *)
Definition observe_cell_def:
  observe_cell Q x = if x IN Q then SOME x else NONE
End

Theorem observe_mark_dead_stack:
  !Q retained stk.
    dead_stack_marker NOTIN Q /\ (!x. MEM x retained ==> x NOTIN Q) ==>
    MAP (observe_cell Q) (mark_dead_stack retained stk) =
    MAP (observe_cell Q) stk
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `stk` >> simp[mark_dead_stack_def] >>
  gen_tac >> Cases_on `MEM h retained` >> simp[observe_cell_def] >>
  gvs[mark_dead_stack_def]
QED

Theorem observe_irrelevant_prefix:
  !Q prefix. EVERY (\x. x NOTIN Q) prefix ==>
    MAP (observe_cell Q) prefix = REPLICATE (LENGTH prefix) NONE
Proof
  gen_tac >> Induct >> simp[observe_cell_def]
QED

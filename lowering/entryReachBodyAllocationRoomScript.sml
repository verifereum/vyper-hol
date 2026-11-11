(* The checked static frontier charge supplies the body allocation room. *)
Theory entryReachBodyAllocationRoom
Ancestors
  allocaFrontierBound exprLoweringProps allocaBudgetProps vyperCompiler
  list finite_map arithmetic words

Theorem entry_alloca_literal_size[local]:
  alloca_lit_size = alloca_size
Proof
  simp[FUN_EQ_THM, alloca_lit_size_def, alloca_size_def]
QED

Theorem entry_pending_allocation_charge[local]:
  pending_alloca_size func s = remaining_alloca_budget (fn_insts func) s
Proof
  simp[pending_alloca_size_def, remaining_alloca_budget_def,
       entry_alloca_literal_size]
QED

Theorem entry_frontier_alloca_room:
  alloca_frontier_inv ctx func inst s /\
  unit_alloca_budget ctx < dimword (:256) ==>
  alloca_room ctx func s
Proof
  strip_tac >>
  `FINITE {g | TC (fn_directly_calls ctx) func.fn_name g}` by
    (irule (cj 1 call_targets_card)) >>
  gvs[alloca_frontier_inv_def, alloca_room_def,
      entry_pending_allocation_charge, unit_alloca_frame_def,
      entry_alloca_literal_size] >> decide_tac
QED

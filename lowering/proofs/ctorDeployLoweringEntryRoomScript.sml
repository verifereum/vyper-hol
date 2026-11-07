Theory ctorDeployLoweringEntryRoom
Ancestors
  ctorDeployMemoryFrontier allocaFrontierBound allocaBudgetProps
  exprLoweringProps vyperCompiler

Theorem deploy_ctor_alloca_size_eq:
  alloca_lit_size = alloca_size
Proof
  simp[FUN_EQ_THM, alloca_lit_size_def, alloca_size_def]
QED

Theorem deploy_ctor_pending_alloca_eq:
  pending_alloca_size func s = remaining_alloca_budget (fn_insts func) s
Proof
  simp[pending_alloca_size_def, remaining_alloca_budget_def,
       deploy_ctor_alloca_size_eq]
QED

Theorem deploy_ctor_frontier_alloca_room:
  alloca_frontier_inv_from k ctx func site s /\
  k + unit_alloca_budget ctx < dimword (:256) ==>
  alloca_room ctx func s
Proof
  simp[alloca_frontier_inv_from_def, alloca_room_def,
       deploy_ctor_pending_alloca_eq, unit_alloca_frame_def,
       deploy_ctor_alloca_size_eq, call_targets_card] >>
  rpt strip_tac >> decide_tac
QED

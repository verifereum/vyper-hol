Theory allocaFrontierRoom
Ancestors
  allocaFrontierBound allocaBudgetProps exprLoweringProps vyperCompiler
  words arithmetic

Theorem registration_frontier_alloca_room:
  alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) ==> alloca_room ctx fn s
Proof
  `alloca_lit_size = alloca_size` by
    (simp[FUN_EQ_THM, exprLoweringPropsTheory.alloca_lit_size_def,
      vyperCompilerTheory.alloca_size_def]) >>
  strip_tac >>
  gvs[allocaFrontierBoundTheory.call_targets_card,
    exprLoweringPropsTheory.alloca_room_def,
    allocaFrontierBoundTheory.alloca_frontier_inv_def,
    exprLoweringPropsTheory.pending_alloca_size_def,
    allocaBudgetPropsTheory.remaining_alloca_budget_def,
    exprLoweringPropsTheory.unit_alloca_frame_def] >> decide_tac
QED

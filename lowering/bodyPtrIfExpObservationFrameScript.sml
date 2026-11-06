Theory bodyPtrIfExpObservationFrame
Ancestors
  bodyPtrDefs loweringPosts exprSimProps exprSimSource exprSimWordArgs
  stmtFragPtr vyperState

(* Initial observations are bookkeeping only for these frames. The actual
   eval_expr premise must still use the explicit marked observation list. *)
Theorem ifexp_ghost_kept_initial_gas:
  ghost_kept ce (es with gas_obs := gs) sa G0 tn0 s0 G tn <=>
  ghost_kept ce es sa G0 tn0 s0 G tn
Proof
  simp[ghost_kept_def]
QED

Theorem ifexp_expr_post_initial_gas:
  expr_post ctx fn ce cx e (es with gas_obs := gs) sa sb s0 ee v op s <=>
  expr_post ctx fn ce cx e es sa sb s0 ee v op s
Proof
  simp[expr_post_def, locals_kept_def]
QED

(* Entry observation lists do not affect protected frame predicates. *)
Theory bodyPtrEnvBuiltinsEntryFrame
Ancestors bodyPtrDefs exprSimDefs vyperState loweringPosts

Theorem expr_post_entry_gas_obs:
  expr_post ctx fn cenv cx e (es with gas_obs := gs) sa sb s0 ee v op s <=>
  expr_post ctx fn cenv cx e es sa sb s0 ee v op s
Proof
  simp[expr_post_def, locals_kept_def]
QED

Theorem ghost_kept_entry_gas_obs:
  ghost_kept cenv (es with gas_obs := gs) sa G0 tn0 s0 G tn <=>
  ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  simp[ghost_kept_def]
QED

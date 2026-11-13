(*
 * Statement targets over the finite-horizon joint judgment: a base target
 * (a local, a module variable, a field or an element of one) resolves to
 * its place and its pointer at one joint endpoint, as expr_sim_full's
 * expression resolves to its value.  targetPlaceSimDefs' target_sim and
 * bodyPtrPopTargetDefs' target_sim_ptr over gas_outcome_full, with the
 * shadow compilation and the initial resources of expr_sim_full.
 *
 * The judgments are bodyFullTargetDefs'.
 *
 * TOP-LEVEL:
 *   body_target_sim_full, body_target_place_sim_full -- a target meeting
 *     target_pre whose indices have their joint judgments has both
 *)
Theory bodyFullTarget
Ancestors
  bodyFullTargetRoots bodyFullTargetDefs bodyFullPreds bodySimFull
  targetPlaceSim targetPlaceSimDefs vyperInterpreter vyperState vyperAST

val _ = Parse.hide "body";

Theorem body_target_sim_full:
  !bt DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env es.
    body_inv tops ctx cenv cx /\
    body_base_target_full_ok cx bt /\
    target_pre cenv cx env bt es ==>
    target_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx env bt es
Proof
  cheat
QED

Theorem body_target_place_sim_full:
  !bt DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env es.
    body_inv tops ctx cenv cx /\
    body_base_target_full_ok cx bt /\
    target_pre cenv cx env bt es ==>
    target_place_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx env bt es
Proof
  cheat
QED

(*
 * Held residual of pop_expr_ptr_ok (bodyPtrPop): pop on a nested target
 * rooted at a local whose place, when the pop runs, only the local's
 * popped history holds (an index popped the array the target points
 * into).  The pointer twin of S1's
 * exprSimPopNestedLocalPopped.pop_nested_local_popped_case
 * (alan-ref/s1-places-pop), with the target's judgment given by
 * body_base_target_ptr_ok in place of S1's pop_target_frag.
 *
 * TOP-LEVEL:
 *   pop_nested_local_popped_case_ptr
 *)
Theory bodyPtrPopResidualNestedLocalPopped
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs targetPlaceSim
  vyperInterpreter vyperState vyperAST

(* RESIDUAL: held per argon ruling 2026-11-08; closed with S1's twin after the vyper v0.5.0b2 repin (vyperlang/vyper#5280 rejects risky target overlap) *)
Theorem pop_nested_local_popped_case_ptr:
  !tops ctx cenv cx env ann bt id ty es d PG func s path t entry err v.
    body_inv tops ctx cenv cx /\
    body_base_target_ptr_ok cx bt /\
    target_root bt = NameTarget id /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    eval_target_place cx bt s = (INL (MemoryPlace id path), t) /\
    lookup_scopes id t.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INR err /\
    read_popped entry.type path entry.popped = SOME v ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

(*
 * Held residual of pop_expr_ptr_ok (bodyPtrPop): pop on a nested target
 * rooted at a local where some index leaves the base's path outside the
 * local's value (~local_target_live: an index popped the array the
 * target points into, so only the local's popped history holds the
 * place).  The pointer twin of S1's
 * exprSimPopNestedLocalPopped.pop_nested_local_popped_case.
 *
 * TOP-LEVEL:
 *   pop_nested_local_popped_case_ptr
 *)
Theory bodyPtrPopResidualNestedLocalPopped
Ancestors
  bodyPtrPopTargetDefs bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs
  targetPlaceSim vyperInterpreter vyperState vyperAST

(* RESIDUAL: held per argon ruling 2026-11-08; closed with S1's twin after the vyper v0.5.0b2 repin (vyperlang/vyper#5280 rejects risky target overlap) *)
Theorem pop_nested_local_popped_case_ptr:
  !tops ctx cenv cx env ann bt id ty es d PG func.
    body_inv tops ctx cenv cx /\
    body_base_target_ptr_ok cx bt /\
    (!x. bt <> NameTarget x) /\
    target_root bt = NameTarget id /\
    ~local_target_live cx id bt /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

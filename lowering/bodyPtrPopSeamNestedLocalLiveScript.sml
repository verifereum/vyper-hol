(*
 * Seam of pop_expr_ptr_ok (bodyPtrPop): pop on a nested target rooted at
 * a local (x[i].pop(), x.a[i].pop(), ...) whose place stays live: if the
 * target's path does not resolve in the local's value when the pop runs,
 * the local has no popped value there either.  The pointer twin of S1's
 * exprSimPopNestedLocal.pop_nested_local_live_case (alan-ref/s1-places-pop),
 * with the target's judgment given by body_base_target_ptr_ok in place of
 * S1's pop_target_frag.  The other nested-local case, a place that only
 * the local's popped history holds, is the held residual
 * bodyPtrPopResidualNestedLocalPopped.
 *
 * TOP-LEVEL:
 *   pop_nested_local_live_vv_ptr
 *)
Theory bodyPtrPopSeamNestedLocalLive
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs targetPlaceSim
  vyperInterpreter vyperState vyperAST

(* Hints, not part of the statement:
   - compile_expr of the pop is compile_get_target_ptr then
     compile_dynarray_pop at the target's header (a Var: bodyPtrPopNestedHeader's
     pop_nested_target_header) in memory
     (bodyPtrPopNestedCompilation's pop_compile_target_decomposition).
   - The target's indices: bodyPtrPopTargetFactor (eval_base_place cuts,
     compile_get_target_ptr cuts, pop_target_index_ptr_premise).
   - The pop suffix's counted pieces are the ones listed at
     bodyPtrPopSeamLocalRoot's pop_local_root_vv_ptr.
   - After each index, its ghost_inv gives the root local's value in memory
     whatever its tainted bytes hold, so the live headers on the target's
     path are untainted.
   - S1's proof of the same case: alan-ref/s1-places-pop/
     exprSimPopNestedLocal*Script.sml.txt. *)
Theorem pop_nested_local_live_vv_ptr:
  !tops ctx cenv cx env ann bt id ty es d PG func.
    body_inv tops ctx cenv cx /\
    body_base_target_ptr_ok cx bt /\
    (!x. bt <> NameTarget x) /\
    target_root bt = NameTarget id /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    (!s path t entry err.
       eval_target_place cx bt s = (INL (MemoryPlace id path), t) /\
       lookup_scopes id t.scopes = SOME entry /\
       evaluate_subscripts entry.type entry.value path = INR err ==>
       read_popped entry.type path entry.popped = NONE) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

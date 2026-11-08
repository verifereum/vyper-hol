(*
 * Seam of pop_expr_ptr_ok (bodyPtrPop): the pop suffix on a nested target
 * rooted at a local (x[i].pop(), x.a[i].pop(), ...) whose base path every
 * index leaves live (local_target_live), given the target's fragment
 * judgment pop_target_frag_ptr.  The pointer twin of S1's
 * exprSimPopNestedLocal.pop_nested_local_live_case.
 *
 * TOP-LEVEL:
 *   pop_nested_local_live_vv_ptr
 *)
Theory bodyPtrPopSeamNestedLocalLive
Ancestors
  bodyPtrPopTargetDefs bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs
  targetPlaceSim vyperInterpreter vyperState vyperAST

(* Hints, not part of the statement:
   - compile_expr of the pop is compile_get_target_ptr then
     compile_dynarray_pop at the target's pointer in memory
     (exprSimPopNestedBase's nested_pop_compile_eq); eval_expr of the pop
     is bind (eval_target_place cx bt) (pop_place cx).  S1's proof
     follows exactly this split (pop_nested_local_live_case and its
     exprSimPopNestedLocal* helpers).
   - local_target_live makes the place's path resolve in the local's
     value when the pop runs: the last index's extend_place checks the
     element against the value at the base's path, which
     local_target_live keeps inside the local's value; a trailing field
     always resolves.  So the length word the pop loads is part of the
     local's value, and ghost_inv's val_in_memory (whatever its tainted
     bytes hold) makes it untainted.
   - target_ptr_ok gives the header pointer the local's site, which
     ghost_inv's ptr_covers covers the local with: the MLOAD/MSTORE access
     checks and the element pointer's ptr_mem_ok/ptr_buf_ok.
   - The pop suffix's counted pieces: bodyPtrPopMemoryHeader,
     bodyPtrPopLengthGuard, bodyPtrPopMemoryStore, bodyPtrPopLengthStore,
     bodyPtrPopInteriorPointer, bodyPtrPopLiveElement (listed at
     bodyPtrPopSeamLocalRoot's pop_local_root_vv_ptr).
   - The new length word is a dynarray_len_at offset of the local, which
     ghost_kept exempts. *)
Theorem pop_nested_local_live_vv_ptr:
  !tops ctx cenv cx env ann bt id ty es d PG func.
    body_inv tops ctx cenv cx /\
    pop_target_frag_ptr d ctx PG func cenv cx env bt es /\
    (!x. bt <> NameTarget x) /\
    target_root bt = NameTarget id /\
    local_target_live cx id bt /\
    expr_body_pre cenv cx env (Pop ann bt) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

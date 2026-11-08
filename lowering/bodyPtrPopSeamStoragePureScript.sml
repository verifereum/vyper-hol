(*
 * Seam of pop_expr_ptr_ok (bodyPtrPop): pop on a nested target rooted at
 * a storage or transient variable whose indices are pure
 * (self.s.a.pop(), self.b[i].pop(), self.m[k].pop()).  The pointer twin
 * of S1's exprSimPopNestedBase.pop_nested_storage_pure_sim, with the
 * target's fragment judgment the pointer twin pop_target_frag_ptr.
 *
 * TOP-LEVEL:
 *   pop_nested_storage_pure_vv_ptr
 *)
Theory bodyPtrPopSeamStoragePure
Ancestors
  bodyPtrPopTargetDefs bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs
  targetPlaceSim targetPlaceLive vyperPureExpr vyperInterpreter vyperState
  vyperAST

(* Hints, not part of the statement:
   - compile_expr of the pop is compile_get_target_ptr then
     compile_dynarray_pop at the target's slot (exprSimPopNestedBase's
     nested_pop_compile_eq, nested_pop_compile_storage_eq): SLOAD/TLOAD of
     the length, the guard, SUB, SSTORE/TSTORE of the new length, the
     element's slot.
   - Pure indices leave storage alone, so the target's place is live when
     the pop reads it: targetPlaceLive's nested_pop_eval_target_live_post
     gives storage_read_live for the length slot and the popped element's
     slots, so stor_taint_ok makes the length word untainted (its bytes
     are not dead) and the popped slots dead after the length store.
   - The root storage pop's pointer case, at a declared variable's slot,
     is bodyPtrPopRootOutcome's compile_pop_storage_normalized_ptr, built
     from the proved bodyPtrPopRoot*, bodyPtrPop*Transfer,
     bodyPtrPopZeroAbort, bodyPtrPopReturned pieces; this case runs the
     same suffix at the target's slot (target_post's place_ptr_rel, and
     target_ptr_ok's untainted, provenance-free pointer).
   - S1's proof of the same case: exprSimPopNestedBase's
     pop_nested_storage_pure_sim (and exprSimPopNestedStorageFrame).
   - The post: post_value_type cenv (Pop ann bt) = ann, and
     expr_has_effect (Pop ann bt). *)
Theorem pop_nested_storage_pure_vv_ptr:
  !tops ctx cenv cx env ann bt ty es d PG func src id ts vd.
    body_inv tops ctx cenv cx /\
    pop_target_frag_ptr d ctx PG func cenv cx env bt es /\
    expr_body_pre cenv cx env (Pop ann bt) es /\
    target_root bt = TopLevelNameTarget (src,id) /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME vd /\
    EVERY pure_expr (target_indices bt) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Pop ann bt) es
Proof
  cheat
QED

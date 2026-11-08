(*
 * Seam of bodyPtrSubscript's subscript_expr_ptr_ok: an element of a static
 * array in memory, laid out at its own type, whose index frames the base.
 *
 * TOP-LEVEL:
 *   subscript_array_framed_memory_ptr
 *)
Theory bodyPtrSubscriptSeamArrayMemory
Ancestors
  bodyPtrSubscriptRejectedSelector bodyPtrSubscriptSignedBounds
  bodyPtrSubscriptCountedAdd
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs loweringPosts context
  exprLowering vyperInterpreter vyperState vyperContext vyperAST

(* The memory half of the pointer twin of S1's
   compile_subscript_array_framed_base_case (exprSimSubscriptArray): a
   static array with no dynamic array inside it, lowered to a memory
   pointer and laid out at its own type (an internal call whose site widens
   the callee's return type is the residual
   bodyPtrSubscriptWidenedResidual), whose source result is no storage
   place, and whose index leaves the source locals and immutables as they
   were.  compile_subscript lowers the base, then the index (lower_value at
   ty), then compile_array_subscript with is_dynamic = F: the bounds check
   against the literal static count (SLT for a signed index, LT, ISZERO,
   OR, ISZERO, ASSERT) and the element address base + idx * elem_size.  The
   base's bytes lie in one of its own allocations or in a live local's
   region and hold no length word, so the index's expr_post and ghost_kept
   keep them and their taint.  The bounds check compares the index with a
   literal count (LT [idx; Lit n]), outside access_ok's two-variable
   comparison clause; the index's ptr_val_ok (a word: untainted, no
   provenance) serves the taint checks, and MUL gives no provenance.
   Hints: the S1 proof is exprSimSubscriptArrayFramed and the
   exprSimSubscriptArray{Compose,Suffix,Source,Frame,Endpoint,Origin}
   theories in this tree; the lane helpers bodyPtrSubscriptBoundsRun,
   bodyPtrSubscriptSignedBounds, bodyPtrSubscriptRejectedSelector and
   bodyPtrSubscriptCountedAdd have the counted bounds check, its abort and
   the address arithmetic. *)
Theorem subscript_array_framed_memory_ptr:
  !cx ann e1 e2 d PG tops ctx func cenv env ty es et n.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_expr_ptr_ok cx e1 /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_type e1 = ArrayT et (Fixed n) /\
    place_type cenv e1 = ValPT (ArrayT et (Fixed n)) /\
    post_value_type cenv e1 = expr_type e1 /\
    (!t r t'. eval_expr cx e2 t = (INL r, t') ==>
              t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tr slot vt t.
       eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    (!ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript ann e1 e2) es
Proof
  cheat
QED

(*
 * Seam of bodyPtrSubscript's subscript_expr_ptr_ok: a subscript of a tuple
 * laid out at its own type.
 *
 * TOP-LEVEL:
 *   subscript_tuple_vv_sim_ptr
 *)
Theory bodyPtrSubscriptSeamTuple
Ancestors
  bodyPtrSubscriptTupleSource bodyPtrSubscriptTupleSuffix
  bodyPtrSubscriptTupleDispatch bodyPtrDefs exprSimHypsDefs loweringPosts
  exprLowering vyperAST

(* A tuple element: the index is a literal (bodyPtrSubscriptTupleDispatch's
   tuple_subscript_pre), and compile_subscript adds the element's constant
   offset to the base's pointer (tuple_subscript_compile), at the base's
   location.  The base's lowered value is laid out at its own type
   (post_value_type cenv obj = expr_type obj), so the offset and the
   element's buffer are inside the base's buffer: an internal call whose
   site widens the callee's return type is the residual
   bodyPtrSubscriptWidenedResidual.  The S1 twin is exprSimTuple's
   compile_subscript_tuple_sim.
   Hints: bodyPtrAttributeSim's attribute_vv_sim_ptr is the same shape (a
   base's expr_vv_sim_ptr, then one ADD of a constant offset) and its
   helpers (bodyPtrAttributeCase, bodyPtrAttributeSummary) do most of the
   per-location work; bodyPtrSubscriptTupleSuffix's
   compile_tuple_subscript_counted is the counted ADD with child coverage,
   and bodyPtrSubscriptTupleSource has the source side. *)
Theorem subscript_tuple_vv_sim_ptr:
  !d ctx PG func cenv cx env ty ann obj idx es tys.
    expr_body_pre cenv cx env (Subscript ann obj idx) es /\
    expr_type obj = TupleT tys /\ place_type cenv obj = ValPT (TupleT tys) /\
    post_value_type cenv obj = expr_type obj /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty obj es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript ann obj idx) es
Proof
  cheat
QED

(*
 * Expression simulation: compile_subscript_array_case, a case of exprSimPlaces on its
 * own so it can be proved apart (see the comment on the theorem).
 *)

Theory exprSimSubscriptArray
Ancestors
  exprSimSource exprSimHypsDefs list exprSimHyps exprSimPop exprSimAttribute exprSimTuple exprSimPopStorage exprSimPopNested
  exprSimArrayIndex
  exprLowering placeTypingProps vyperAST vyperTypeSystem vyperTypeCallGraph

(* An element of a static or dynamic array, with the bounds-check abort.
   Cheated: compile_subscript lowers the index after the base, and the
   base's value_vv must still hold its value when the index's fragment
   ends.  Where the base points into a live local's region (x[i] for a
   local x), the index can change that local (x[x.pop()]), and expr_post
   then says only that the local holds its new value, at its region: the
   base's pointer is the local's place at a path, but vv_holds does not say
   so, so the element's value at the base's pointer does not follow.  The
   proof needs vv_holds to relate a pointer into a local's region to the
   place it reads (a place-pointer relation), or a fragment for the index
   that keeps the base's bytes (exprSimOperands keeps a base in the
   expression's own allocations only).  The bounds check itself, a source
   RuntimeError for an index out of range against compile_array_subscript's
   ASSERT, which aborts, is in expr_exit's allowance (exprSimArrayIndex).
   A dynamic array in code (an immutable, LocCode) reads its length with
   compile_ptr_load's compile_imm_load_word (ILOAD or DLOAD), for which
   exprSimArrayIndex has no array_len_ok lemma yet. *)
Theorem compile_subscript_array_case:
  !nocalls ctx func cenv cx ann obj idx et bd.
    expr_vv_case nocalls ctx func cenv cx obj /\
    (!s tv t. eval_expr cx obj s = (INL tv, t) ==>
              expr_sim_case nocalls ctx func cenv cx idx) /\
    expr_type obj = ArrayT et bd /\ place_type cenv obj = ValPT (ArrayT et bd) ==>
    expr_vv_case nocalls ctx func cenv cx (Subscript ann obj idx)
Proof
  cheat
QED

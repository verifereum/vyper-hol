(*
 * RESIDUAL of bodyPtrSubscript's subscript_expr_ptr_ok: an array subscript
 * whose base's place the index's fragment may not keep.  The pointer twin
 * of S1's compile_subscript_array_place_base_case (exprSimSubscriptArray),
 * which S1 admits too: vv_post does not tie the base's pointer to its
 * source place, so an index that writes storage, pops, or changes a local
 * leaves the base's place stale (the witnesses are in S1's comment).  A
 * place-pointer clause in vv_post replaces most of it, on S1's side first.
 *
 * TOP-LEVEL:
 *   body_subscript_array_place_base_ptr
 *)
Theory bodyPtrSubscriptArrayPlaceResidual
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs loweringPosts context
  exprLowering vyperInterpreter vyperState vyperContext vyperAST

(* Every array subscript, of a base laid out at its own type, but the
   framed ones of bodyPtrSubscriptSeamArrayMemory and
   bodyPtrSubscriptSeamArrayCode: a base in storage or transient storage, a
   dynamic array or one with a dynamic array inside it in memory, a base
   whose source result is a storage place, a runtime immutable in the
   constructor, or an index that changes the locals or the immutables. *)
Theorem body_subscript_array_place_base_ptr:
  !cx ann e1 e2 d PG tops ctx func cenv env ty es et bd.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_expr_ptr_ok cx e1 /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_type e1 = ArrayT et bd /\ place_type cenv e1 = ValPT (ArrayT et bd) /\
    post_value_type cenv e1 = expr_type e1 /\
    ~((!t r t'. eval_expr cx e2 t = (INL r, t') ==>
                t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
      (!s tr slot vt t.
         eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
      ((~cenv.ce_is_ctor /\
        !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocCode) \/
       ((?n. bd = Fixed n) /\
        (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
        !ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocMemory))) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript ann e1 e2) es
Proof
  (* RESIDUAL: held per argon ruling 2026-11-08, as S1 holds its twin *)
  cheat
QED

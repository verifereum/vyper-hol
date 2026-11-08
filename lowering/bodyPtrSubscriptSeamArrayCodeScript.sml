(*
 * Seam of bodyPtrSubscript's subscript_expr_ptr_ok: an element of a
 * runtime immutable array whose index frames the base.
 *
 * TOP-LEVEL:
 *   subscript_array_framed_code_ptr
 *)
Theory bodyPtrSubscriptSeamArrayCode
Ancestors
  bodyPtrSubscriptRejectedSelector bodyPtrSubscriptSignedBounds
  bodyPtrSubscriptCountedAdd
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs loweringPosts context
  exprLowering vyperInterpreter vyperState vyperContext vyperAST

(* The code half of the pointer twin of S1's
   compile_subscript_array_framed_base_case (exprSimSubscriptArray): an
   array lowered to a code pointer outside the constructor (a runtime
   immutable, in the data section), laid out at its own type, whose source
   result is no storage place, and whose index leaves the source locals and
   immutables as they were.  compile_subscript lowers the base, then the
   index (lower_value at ty), then compile_array_subscript: for a dynamic
   array the length through compile_ptr_load's compile_imm_load_word (DLOAD
   at runtime), the bounds check, and the element address.  immutables_rel
   relates the data section to the unchanged source immutables, so the
   base's place reads at the index's end what it read before.  ptr_vv_ok
   asks of a code pointer an untainted operand with no provenance
   (op_prov G p.ptr_operand = NONE), which the base's ptr_vv_ok gives for
   the base's operand and ghost_kept keeps across the index; out_prov of
   ADD takes its first operand's provenance and MUL's is none.  For a
   dynamic array the bounds check compares the index with a freshly loaded
   length variable (LT [idx; len]), so access_ok's two-variable comparison
   clause needs the index's provenance to be none, which a word index's
   ptr_val_ok gives.
   Hints: the S1 proof is exprSimSubscriptArrayFramed and the
   exprSimSubscriptArray{Compose,Suffix,Source,Frame,Endpoint,Origin}
   theories in this tree; the lane helpers bodyPtrSubscriptBoundsRun,
   bodyPtrSubscriptSignedBounds, bodyPtrSubscriptRejectedSelector and
   bodyPtrSubscriptCountedAdd have the counted bounds check, its abort and
   the address arithmetic. *)
Theorem subscript_array_framed_code_ptr:
  !cx ann e1 e2 d PG tops ctx func cenv env ty es et bd.
    (!s res t. eval_expr cx e1 s = (INL res,t) ==> body_expr_ptr_ok cx e2) /\
    body_expr_ptr_ok cx e1 /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_type e1 = ArrayT et bd /\
    place_type cenv e1 = ValPT (ArrayT et bd) /\
    post_value_type cenv e1 = expr_type e1 /\
    (!t r t'. eval_expr cx e2 t = (INL r, t') ==>
              t'.scopes = t.scopes /\ t'.immutables = t.immutables) /\
    (!s tr slot vt t.
       eval_expr cx e1 s <> (INL (PlaceR (StoragePlace tr slot vt)), t)) /\
    ~cenv.ce_is_ctor /\
    (!ty st. vv_location (FST (compile_expr cenv ty e1 st)) = SOME LocCode) ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Subscript ann e1 e2) es
Proof
  cheat
QED

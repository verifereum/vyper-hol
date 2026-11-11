(*
 * The pointer twin of S1's bodySimMakeArrayWidened: an array literal with
 * an element that is an internal call whose lowered value type differs
 * from its annotated type, for bodyPtrMakeArray's make_array_expr_ptr_ok.
 *
 * RESIDUAL, HELD for the posts-interface wave (Decision 18): its proof
 * needs expr_sim_ptr/expr_vv_sim_ptr to state a widened internal call's
 * pointer facts at post_value_type, which this branch does not have yet.
 * It lands with body_intcall_widened_ptr.  Not open work here.
 *
 * TOP-LEVEL:
 *   body_make_array_widened_call_elem_ptr - that case
 *)
Theory bodyPtrMakeArrayWidened
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps vyperAST
  vyperInterpreter vyperState vyperContext vyperTypeCallGraph list

val _ = Parse.hide "body";

Theorem body_make_array_widened_call_elem_ptr:
  !cx ty t n es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH es) ==>
     body_exprs_ptr_ok cx es) ==>
    !d PG tops ctx func cenv env ty' st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (Builtin ty (MakeArray t n) es) st /\
      (?e. MEM e es /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) ==>
      expr_sim_ptr d ctx PG func cenv cx ty' (Builtin ty (MakeArray t n) es) st /\
      expr_vv_sim_ptr d ctx PG func cenv cx ty' (Builtin ty (MakeArray t n) es) st
Proof
  cheat
QED

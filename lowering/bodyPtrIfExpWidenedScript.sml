(*
 * The pointer twin of S1's bodySimIfExpWidened: a ternary with an arm whose
 * value the lowering lays out differently from its source type, for
 * bodyPtrIfExp's ifexp_expr_ptr_ok.
 *
 * RESIDUAL, HELD with S1's body_ifexp_widened_call_arm: describing a widened
 * internal call's value at its lowered type is the internal-call
 * simulation's work.  Not open work here.
 *
 * TOP-LEVEL:
 *   body_ifexp_widened_call_arm_ptr - that case
 *)
Theory bodyPtrIfExpWidened
Ancestors
  exprPtrUnwrap bodyPtrPreds bodyPtrDefs bodySim exprSimHyps loweringPosts
  context vyperAST vyperInterpreter vyperState vyperContext
  vyperTypeCallGraph list

(* RESIDUAL: widened internal-call IfExp arm, held with S1's
   body_ifexp_widened_call_arm *)
Theorem body_ifexp_widened_call_arm_ptr:
  !cx v5 e1 e2 e3.
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ptr_ok cx e2) /\
    (!s'' tv t. eval_expr cx e1 s'' = (INL tv,t) ==> body_expr_ptr_ok cx e3) /\
    body_expr_ptr_ok cx e1 ==>
    !d PG tops ctx func cenv env ty st.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (IfExp v5 e1 e2 e3) st /\
      (?e. (e = e2 \/ e = e3) /\
           ~((int_calls_expr e = [] \/
              same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
             post_value_type cenv e = expr_type e)) ==>
      expr_sim_ptr d ctx PG func cenv cx ty (IfExp v5 e1 e2 e3) st /\
      expr_vv_sim_ptr d ctx PG func cenv cx ty (IfExp v5 e1 e2 e3) st
Proof
  cheat
QED

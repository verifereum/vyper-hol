(* Operand structure only. Arity and source operand preconditions are already
   exported by exprSimOperators: expr_body_pre_bop_args and expr_body_pre_bop.
   Keep those shared boundaries rather than duplicating their statements. *)
Theory bodyPtrBopOperands
Ancestors
  bodyPtrPreds exprSimOperators

Theorem body_exprs_ptr_ok_pair:
  body_exprs_ptr_ok cx [e1; e2] <=>
  body_expr_ptr_ok cx e1 /\
  ((?s tv t s1 v t1.
      eval_expr cx e1 s = (INL tv,t) /\
      read_result cx tv s1 = (INL v,t1)) ==>
   body_expr_ptr_ok cx e2)
Proof
  simp[bodyPtrPredsTheory.body_exprs_ptr_ok_def]
QED

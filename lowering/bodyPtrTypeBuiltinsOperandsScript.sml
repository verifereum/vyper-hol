Theory bodyPtrTypeBuiltinsOperands
Ancestors
  bodyPtrTypeBuiltinsIndexEntry bodyPtrPreds

Theorem body_expr_ptr_ok_sim:
  !cx e tops ctx cenv env es d PG func ty.
    body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env e es ==>
    expr_sim_ptr d ctx PG func cenv cx ty e es
Proof
  simp[body_expr_ptr_ok_def] >> metis_tac[]
QED

Theorem body_expr_ptr_ok_vv_sim:
  !cx e tops ctx cenv env es d PG func ty.
    body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env e es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es
Proof
  simp[body_expr_ptr_ok_def] >> metis_tac[]
QED

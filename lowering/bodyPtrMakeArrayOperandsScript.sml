(* Operand preconditions are transported to the current source state.
   The tail pointer hypothesis is available only after a successful read. *)
Theory bodyPtrMakeArrayOperands
Ancestors
  bodyPtrPreds exprSimSource exprSimDefs bodySim vyperAST

Theorem make_array_operand_pre:
  expr_body_pre cenv cx env (Builtin ann (MakeArray t n) args) es /\
  MEM e args /\ expr_sim_inv cenv cx env es' ==>
  expr_body_pre cenv cx env e es'
Proof
  strip_tac >> irule expr_body_pre_builtin_arg >> simp[] >>
  qexistsl_tac [`ann`, `args`, `MakeArray t n`, `es`] >> simp[]
QED

Theorem body_exprs_ptr_ok_read_tail:
  body_exprs_ptr_ok cx (e::es) /\
  eval_expr cx e s = (INL tv,t) /\ read_result cx tv s1 = (INL v,t1) ==>
  body_exprs_ptr_ok cx es
Proof
  simp[body_exprs_ptr_ok_def] >> metis_tac[]
QED

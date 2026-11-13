Theory bodyPtrBopSealState
Ancestors
  exprLoweringProps

(* alloca_room pins the current function to the unchanged context.  Therefore
   replacing the function's code cannot preserve this premise merely by
   showing that the replacement has a smaller allocation budget. *)
Theorem bop_alloca_room_function_unique:
  alloca_room ctx f s /\ alloca_room ctx g t /\ f.fn_name = g.fn_name ==>
  f = g
Proof
  simp[alloca_room_def] >> metis_tac[optionTheory.SOME_11]
QED

Theorem bop_stmt_state_rel_function_unique:
  stmt_state_rel ctx f cenv cx es s /\
  stmt_state_rel ctx g cenv' cx' es' t /\ f.fn_name = g.fn_name ==>
  f = g
Proof
  simp[stmt_state_rel_def] >> metis_tac[bop_alloca_room_function_unique]
QED

(* Seam 2 joint induction, For family: iteration over an array. *)
Theory bodyIntCallFamStmtForArray
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtForArrayResources

Theorem intcall_stmts_producer_for_array:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  intcall_stmts_producer fp stmts ==>
  intcall_stmts_producer fp [For id fty (Array arr) bound stmts]
Proof
  cheat
QED

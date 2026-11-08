(* Seam 2 joint induction, a family leaf of the stmt step: Return. *)
Theory bodyIntCallFamStmtReturn
Ancestors
  bodyIntCallJointContract

Theorem intcall_return_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  (?eo. st = Return eo) ==>
  intcall_stmts_producer fp [st]
Proof
  cheat
QED

(* Seam 2 joint induction, a family leaf of the stmt step: Raise and Assert. *)
Theory bodyIntCallFamStmtExit
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtExitReason

Theorem intcall_exit_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  ((?r. st = Raise r) \/ (?e r. st = Assert e r)) ==>
  intcall_stmts_producer fp [st]
Proof
  cheat
QED

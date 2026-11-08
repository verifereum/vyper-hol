(* Seam 2 joint induction, a family leaf of the stmt step: Raise, Assert and Log. *)
Theory bodyIntCallFamStmtExit
Ancestors
  bodyIntCallJointContract

Theorem intcall_exit_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  ((?r. st = Raise r) \/ (?e r. st = Assert e r) \/ (?n es. st = Log n es)) ==>
  intcall_stmts_producer fp [st]
Proof
  cheat
QED

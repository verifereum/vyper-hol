(* Seam 2 joint induction, a family leaf of the stmt step: Log. *)
Theory bodyIntCallFamStmtLog
Ancestors
  bodyIntCallJointContract

Theorem intcall_log_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  (?n es. st = Log n es) ==>
  intcall_stmts_producer fp [st]
Proof
  cheat
QED

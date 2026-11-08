(* Seam 2 joint induction, a family leaf of the stmt step: If. *)
Theory bodyIntCallFamStmtIf
Ancestors
  bodyIntCallJointContract

Theorem intcall_if_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  (?e s1 s2. st = If e s1 s2) ==>
  intcall_stmts_producer fp [st]
Proof
  cheat
QED

(* Seam 2 joint induction, a family leaf of the stmt step: Log.
   bodyIntCallFamStmtLogSuffixTheory.intcall_log_suffix_run is the frozen
   suffix run with its memory and allocation frame. *)
Theory bodyIntCallFamStmtLog
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtLogSuffix
  bodyIntCallFamStmtLogArgsFrame bodyIntCallFamStmtLogGas
  bodyIntCallFamStmtLogResource bodyIntCallFamStmtLogReady
  bodyIntCallFamStmtLogPost

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

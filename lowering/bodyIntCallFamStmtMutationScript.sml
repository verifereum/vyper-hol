(* Seam 2 joint induction, a family leaf of the stmt step: declarations and mutations. *)
Theory bodyIntCallFamStmtMutation
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtMutationResource
  bodyIntCallFamStmtMutationLocalStore bodyIntCallFamStmtMutationResourceLanding
  bodyIntCallFamStmtMutationAppendSuffix

Theorem intcall_mutation_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  ((?x ty e. st = AnnAssign x ty e) \/ (?tg e. st = Assign tg e) \/
   (?ty tg op e. st = AugAssign ty tg op e) \/ (?tg e. st = Append tg e)) ==>
  intcall_stmts_producer fp [st]
Proof
  cheat
QED

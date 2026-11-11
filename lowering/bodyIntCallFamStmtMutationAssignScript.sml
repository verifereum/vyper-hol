(* Seam 2 joint induction, a family leaf of the mutation step: Assign.
   Exactly the Assign instance of intcall_mutation_stmt_step.  Assigns to a
   target whose indices have effects go through the held
   intcall_assign_effectful_index_step (bodyIntCallFamStmtMutationEffectful). *)
Theory bodyIntCallFamStmtMutationAssign
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtMutationEffectful

Theorem intcall_assign_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size (Assign tg rhs) ==>
        intcall_stmts_producer fp ss) ==>
  intcall_stmts_producer fp [Assign tg rhs]
Proof
  cheat
QED

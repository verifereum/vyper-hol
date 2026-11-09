(* Seam 2 joint induction, a family leaf of the stmt step: declarations and mutations. *)
Theory bodyIntCallFamStmtMutation
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtMutationResource
  bodyIntCallFamStmtMutationEffectful
  bodyIntCallFamStmtMutationLocalStore bodyIntCallFamStmtMutationResourceLanding
  bodyIntCallFamStmtMutationAppendSuffix bodyIntCallFamStmtMutationAppendExec
  bodyIntCallFamStmtMutationDeclEntry bodyIntCallFamStmtMutationDeclAlloc

(* A pending declaration cannot use the current expression-producer entry.
   The new compile binding is present before the source local is introduced. *)
Theorem intcall_joint_res_requires_declared_binding:
  intcall_joint_res fp ce env es sa s /\
  FLOOKUP ce.ce_vars id = SOME loc ==>
  id IN FDOM env.var_types
Proof
  simp[intcall_joint_res_def, intcall_expr_res_def, bodySimTheory.ce_locals_declared_def] >>
  metis_tac[]
QED

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

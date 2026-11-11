(* Seam 2 joint induction, a family leaf of the mutation step: Assign.
   Exactly the Assign instance of intcall_mutation_stmt_step.  Assigns to a
   target whose indices have effects go through the held
   intcall_assign_effectful_index_step (bodyIntCallFamStmtMutationEffectful). *)
Theory bodyIntCallFamStmtMutationAssign
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtMutationEffectful
  bodyIntCallFamStmtMutationAssignResolveRoot

(* Probe boundary: flat tuple assignment does not admit a local subscript
   destination. In particular, swapping two array-valued members of a local
   tuple through x[1], x[0] is outside supported_assignment, independently
   of RHS typing or whether an IfExp returns an aliasing pointer. *)
Theorem assign_tuple_local_subscript_rejected:
  MEM (BaseTarget (SubscriptTarget (NameTarget nm) key)) gs ==>
  ~supportedStmts$supported_assignment tops bindings (TupleTarget gs) rhs
Proof
  simp[supportedStmtsTheory.supported_assignment_def, listTheory.EVERY_MEM] >>
  strip_tac >> disj2_tac >>
  qexists `BaseTarget (SubscriptTarget (NameTarget nm) key)` >>
  simp[supportedStmtsTheory.supported_target_def]
QED

Theorem intcall_assign_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size (Assign tg rhs) ==>
        intcall_stmts_producer fp ss) ==>
  intcall_stmts_producer fp [Assign tg rhs]
Proof
  cheat
QED

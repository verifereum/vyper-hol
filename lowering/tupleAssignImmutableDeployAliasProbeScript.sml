(* Store-alias diagnostic: audit the supported syntax before constructing
   an execution. These exclusions do not assert tuple simulation or ownership. *)
Theory tupleAssignImmutableDeployAliasProbe
Ancestors
  supportedStmts supportedTargets supportedExprs supportedTypes
  tupleAssignImmutableDeploySnapshot

(* The borrowed IfExp computation in Snapshot is real compiler behaviour,
   but a tuple-typed IfExp cannot satisfy supported_stmt's RHS premise.
   In particular a tuple of arrays does not evade the scalar-tuple guard:
   it fails supported_value_type instead. *)
Theorem tuple_immutable_alias_ifexp_excluded:
  ~supported_stmt tops bindings
    (Assign (TupleTarget gs) (IfExp (TupleT tys) c x y))
Proof
  strip_tac >>
  gvs[supportedStmtsTheory.supported_stmt_def,
       supportedStmtsTheory.supported_assignment_def,
       supportedExprsTheory.supported_expr_def,
       supportedExprsTheory.supported_pure_expr_def,
       supportedExprsTheory.supported_effect_expr_def,
       supportedTypesTheory.supported_value_type_def,
       supportedTypesTheory.supported_tuple_type_def,
       supportedTypesTheory.supported_scalar_type_def,
       supportedTypesTheory.supported_word_type_def,
       supportedTypesTheory.supported_string_type_def,
       combinTheory.o_DEF] >>
  fs[listTheory.EVERY_MEM, listTheory.EXISTS_MEM] >>
  metis_tac[supportedTypesTheory.supported_scalar_type_def]
QED

(* The proposed early overwrite of a local field is independently rejected:
   tuple assignments admit supported_target, not supported_target_info. *)
Theorem tuple_immutable_alias_local_index_excluded:
  ~supported_stmt tops bindings
    (Assign (TupleTarget
      (BaseTarget (SubscriptTarget (NameTarget name) key) :: gs)) e)
Proof
  strip_tac >>
  gvs[supportedStmtsTheory.supported_stmt_def,
       supportedStmtsTheory.supported_assignment_def,
       supportedStmtsTheory.supported_target_def]
QED

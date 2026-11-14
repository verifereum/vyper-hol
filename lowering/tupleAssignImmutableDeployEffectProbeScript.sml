(* Bounded effectful-index audit.  This is not a simulation or ownership
   theorem: the nonstaging IfExp caller proposed for the hazard is excluded
   by supported_stmt, even when its target index really is effectful.

   Source order: evaluate_def reads the Assign RHS before assign_tuple_targets;
   eval_base_place then evaluates and reads each subscript key before the
   corresponding write. compile_stmt/compile_tuple_unpack likewise lower the
   RHS before compile_tuple_store_all resolves the targets in order.

   A storage Pop is a supported effect, unlike a local-memory Pop.  It can
   change storage but not caller scopes (aug_place_supported_expr_scopes).
   Neither scope equality nor this syntax exclusion claims preservation of
   arbitrary compiled memory bytes. *)
Theory tupleAssignImmutableDeployEffectProbe
Ancestors
  tupleAssignImmutableDeployAliasProbe bodySimAugPlaceScopes
  supportedStmts supportedTargets supportedExprs supportedExprForms
  supportedDecls supportedTypes stmtLowering

Theorem tuple_immutable_effectful_index_candidate:
  let tops =
    [VariableDecl Private Storage "indices"
       (ArrayT (BaseT (UintT 256)) (Dynamic 2)) (SOME 0);
     VariableDecl Private Immutable "imm"
       (ArrayT (BaseT BoolT) (Fixed 1)) NONE];
      key = Pop (BaseT (UintT 256))
        (TopLevelNameTarget (NONE,"indices"));
      bt = SubscriptTarget (TopLevelNameTarget (NONE,"indices")) key;
      rhs = IfExp (TupleT [BaseT (UintT 256);
                           ArrayT (BaseT BoolT) (Fixed 1)]) c x y
  in
    supported_target tops [] bt /\
    ~supported_target_pure tops bt /\
    IS_SOME (supported_immutable_type tops (NONE,"imm")) /\
    ~is_memory_view rhs /\
    ~supported_stmt tops []
      (Assign (TupleTarget
        [BaseTarget bt; BaseTarget (TopLevelNameTarget (NONE,"imm"))]) rhs) /\
    (!cx s r s'. eval_expr cx key s = (r,s') ==> s'.scopes = s.scopes)
Proof
  simp[LET_THM, tuple_immutable_alias_ifexp_excluded,
       stmtLoweringTheory.is_memory_view_def,
       supportedTargetsTheory.supported_target_pure_def,
       supportedExprsTheory.supported_pure_expr_def] >>
  conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  metis_tac[aug_place_top_level_pop_scopes]
QED

(* Pop cannot produce a tuple under the declaration/type agreement of the
   frozen assignment caller. No allocation or borrowed-value claim is used. *)
Theory tupleAssignImmutableDeployPopBoundary
Ancestors
  bodySim exprSimHypsDefs supportedExprForms bodyStorageMetadata
  vyperTypeContractStaticMaps vyperPlaceResultTyping vyperTypeSystem
  vyperTypeInvariants supportedTypes supportedStmts supportedExprs

Theorem tuple_immutable_pop_excluded[local]:
  !tops cx env es tys id.
    env_consistent env cx es /\
    get_module_code cx NONE = SOME tops /\
    ALL_DISTINCT
      (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
    supported_storage_dynamic_array tops id ==>
    ~well_typed_expr env (Pop (TupleT tys) (TopLevelNameTarget id))
Proof
  rpt gen_tac >> strip_tac >> strip_tac >>
  PairCases_on `id` >>
  Cases_on `supported_variable_decl tops (id0,id1)` >>
  gvs[supported_storage_dynamic_array_def] >>
  rename1 `supported_variable_decl tops (src,name) = SOME info` >>
  PairCases_on `info` >>
  Cases_on `info2` >> gvs[] >>
  rename1 `ArrayT elem bd` >> Cases_on `bd` >> gvs[] >>
  Cases_on `info0` >> Cases_on `info1` >> Cases_on `info3` >>
  gvs[] >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  gvs[Once well_typed_expr_def] >>
  drule_all vyperPlaceResultTypingTheory.type_place_target_global_lookup >>
  strip_tac >>
  `(?tr. find_var_decl_by_name name tops =
      SOME (StorageVarDecl tr (ArrayT elem (Dynamic n)),name))` by
    metis_tac[find_var_decl_by_name_SOME_storage_var_Storage,
              find_var_decl_by_name_SOME_storage_var_Transient] >>
  gvs[env_consistent_def, env_immutables_consistent_def] >>
  first_x_assum drule >> gvs[supported_full_word_type_def]
QED

(* Caller discharge ledger: body_inv supplies module identity and declaration
   uniqueness; expr_sim_inv supplies source environment consistency; the
   assignment typecheck supplies RHS typing; support supplies the storage
   dynamic-array form. These are unchanged frozen antecedents. *)
Theorem tuple_immutable_pop_caller_excluded:
  !tops bindings ctx cenv cx env es ret_ty gs tys id env'.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
    supported_stmt tops bindings
      (Assign (TupleTarget gs) (Pop (TupleT tys) (TopLevelNameTarget id))) /\
    type_stmt env ret_ty
      (Assign (TupleTarget gs) (Pop (TupleT tys) (TopLevelNameTarget id))) =
        SOME env' ==> F
Proof
  rpt gen_tac >> strip_tac >>
  `env_consistent env cx es /\ get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops))` by
    gvs[body_inv_def, expr_sim_inv_def] >>
  `well_typed_expr env (Pop (TupleT tys) (TopLevelNameTarget id))` by
    gvs[Once type_stmt_def, AllCaseEqs()] >>
  `supported_storage_dynamic_array tops id` by
    gvs[supportedStmtsTheory.supported_stmt_def,
        supportedStmtsTheory.supported_assignment_def,
        supportedExprsTheory.supported_expr_def,
        supportedExprsTheory.supported_pure_expr_def,
        supportedExprsTheory.supported_effect_expr_def] >>
  metis_tac[tuple_immutable_pop_excluded]
QED

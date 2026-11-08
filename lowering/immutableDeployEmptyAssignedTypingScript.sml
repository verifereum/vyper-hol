(* Assignability obstruction for the constructor containing the assignment. *)
Theory immutableDeployEmptyAssignedTyping
Ancestors
  immutableDeployEmptyAssignedSource immutableDeployEmptyAssignedCode
  immutableDeployEmptyValid immutableDeployEmptyStacked immutableDeployEmptySource
  immutableDeployEmptyDeployment vyperContext vyperTypeInvariants vyperTypeSystem
  vyperTypeInitialState

Theorem assigned_immutable_empty_type_not_assignable:
  ~assignable_type (get_tenv assigned_immutable_cx) (StructT (NONE,"Empty"))
Proof
  simp[assignable_type_def] >> EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem assigned_immutable_metadata_admissible:
  env_context_consistent empty_immutable_env assigned_immutable_cx
Proof
  simp[env_context_consistent_def] >>
  EVAL_TAC >>
  simp[vyperInterpreterTheory.lookup_function_def,
       vyperTypeContractTheory.function_live_def,
       vyperStateTheory.lookup_flag_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> EVAL_TAC >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE,
      vyperStateTheory.find_var_decl_by_name_def]
QED

Theorem assigned_immutable_functions_not_typed:
  ~functions_well_typed assigned_immutable_cx
Proof
  strip_tac >>
  `get_module_code assigned_immutable_cx NONE = SOME assigned_immutable_tops /\
   vyperInterpreter$lookup_callable_function assigned_immutable_cx.in_deploy
     "__init__" assigned_immutable_tops =
     SOME (Payable,F,[],[],NoneT,[assigned_immutable_stmt]) /\
   vyperTypeContract$context_function_live assigned_immutable_cx (NONE,"__init__")`
    by EVAL_TAC >>
  mp_tac assigned_immutable_metadata_admissible >> strip_tac >>
  drule_all functions_well_typed_callable_body_env_base >> strip_tac >>
  gvs[type_stmt_def, assigned_immutable_stmt_def,
      empty_immutable_expr_def, empty_immutable_env_def] >>
  `~assignable_type (type_env empty_immutable_tops)
      (expr_type (StructLit (StructT (NONE,"Empty")) (NONE,"Empty") []))`
    by (EVAL_TAC >> simp[finite_mapTheory.FLOOKUP_UPDATE]) >>
  gvs[]
QED

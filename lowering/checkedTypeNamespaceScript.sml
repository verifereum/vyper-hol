(* Evaluated types in a singleton use only unqualified declarations. *)
Theory checkedTypeNamespace
Ancestors
  supportedStmtTraverse supportedTypes vyperContext vyperValue
  vyperAST vyperTypeSystem finite_map pair list

Triviality type_env_qualified_lookup:
  !tops src name. FLOOKUP (type_env tops) (SOME src,name) = NONE
Proof
  simp[type_env_def] >> Induct >> simp[type_env_for_module_def] >> Cases >>
  rw[type_env_for_module_def, FLOOKUP_UPDATE]
QED

Triviality singleton_evaluated_type_namespace:
  (!tenv ty. tenv = type_env tops /\ IS_SOME (evaluate_type tenv ty) ==>
     supported_type_namespace ty) /\
  (!tenv ts acc. tenv = type_env tops /\ IS_SOME (evaluate_types tenv ts acc) ==>
     supported_types_namespace ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[evaluate_type_def, supported_type_namespace_def, optionTheory.IS_SOME_EXISTS,
      AllCaseEqs()] >>
  rename1 `supported_main_nsid nsid` >> PairCases_on `nsid` >>
  Cases_on `nsid0` >> gvs[supported_main_nsid_def, type_env_qualified_lookup]
QED

Theorem singleton_well_formed_type_namespace:
  well_formed_type (type_env tops) ty ==> supported_type_namespace ty
Proof
  rw[well_formed_type_def] >> metis_tac[singleton_evaluated_type_namespace]
QED

Definition unqualified_struct_metadata_def:
  unqualified_struct_metadata sf <=>
    FEVERY (\(_,fields). EVERY (supported_type_namespace o FST o SND) fields) sf
End

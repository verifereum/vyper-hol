(* Source invariant boundaries for the nested internal call return. *)
Theory bodyIntCallFamCallIntReturnResources
Ancestors
  bodyIntCallFamCallIntReturnFrame exprSimHypsDefs vyperPlaceWriteSoundness
  vyperTypeInvariants vyperEvalOutcomeSuffix exprOracleStorageInterfaces
  vyperCallOutcomeStorage list

Theorem expr_sim_inv_source_frame:
  expr_sim_inv ce cx env es /\ ee.scopes = es.scopes /\
  immutable_metadata_frame es ee /\ state_well_typed ee /\
  accounts_well_typed ee.accounts /\ contract_storage_well_formed cx ee /\
  outcome_suffix es.outcomes ee.outcomes ==>
  expr_sim_inv ce cx env ee
Proof
  strip_tac >>
  `env_immutables_consistent env cx ee` by
    (irule env_immutables_consistent_metadata_frame >>
     fs[expr_sim_inv_def, env_consistent_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `oracle_storage_ok cx ee` by
    (irule oracle_storage_ok_suffix >> qexists `es` >>
     fs[expr_sim_inv_def]) >>
  gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def,
      outcomes_accounts_typed_def, outcome_suffix_def, EVERY_APPEND] >>
  metis_tac[]
QED

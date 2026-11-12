(* Default arguments evaluate in an empty frame and restore only scopes. *)
Theory vyperExternalDefaultsFiniteStorage
Ancestors
  vyperFiniteStoragePreservation vyperStorageFootprint vyperInterpreter

Theorem eval_external_defaults_storage_well_formed_on:
  well_typed_exprs env es /\
  runtime_consistent env cx (st with scopes := [FEMPTY]) /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  storage_observations_ok cx H rt.storage_trace /\
  eval_external_defaults cx es st = (res,rt) ==>
  storage_well_formed_on cx rt (FST H)
Proof
  simp[eval_external_defaults_run] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  simp[] >> strip_tac >> gvs[] >>
  rename1 `eval_exprs cx es (st with scopes := [FEMPTY]) = (out,u)` >>
  `storage_well_formed_on cx (st with scopes := [FEMPTY]) (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `storage_well_formed_on cx u (FST H)` by
    (irule (cj 6 eval_storage_well_formed_on_mutual) >>
     metis_tac[]) >>
  irule (iffRL storage_well_formed_on_backends) >>
  goal_assum (drule_at Any) >> simp[]
QED

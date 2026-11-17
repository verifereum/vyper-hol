(* Finite-storage interface for a checked explicit external body.
   Wrapper transport and observation-prefix reasoning belong to the caller. *)
Theory vyperExternalBodyFiniteStorage
Ancestors
  vyperFiniteStoragePreservation vyperStorageFootprint
  vyperTypeContractSoundness vyperTypeExternalDefaults vyperTypeExprSoundness

val _ = Parse.hide "body";

(* The general adapter consumes readiness of the actual body-entry state. *)
Theorem checked_explicit_external_body_storage_well_formed_on_current:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  context_well_typed cx /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\
  body_entry_ready art cx scope st /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace /\
  eval_stmts cx body st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  strip_tac >>
  drule_all checked_explicit_external_body_setup_current >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (gvs[] >> drule_all checked_explicit_external_body_call_evaluation_safe >> simp[]) >>
  irule (cj 2 eval_storage_well_formed_on_mutual) >> simp[] >>
  qexistsl [`env_body`, `env_after`, `res`, `ret`, `body`, `st`] >>
  gvs[runtime_consistent_def]
QED

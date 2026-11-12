(* Finite-storage interface for a checked explicit external body.
   Wrapper transport and observation-prefix reasoning belong to the caller. *)
Theory vyperExternalBodyFiniteStorage
Ancestors
  vyperFiniteStoragePreservation vyperStorageFootprint
  vyperTypeContractSoundness vyperTypeExternalDefaults vyperTypeExprSoundness

val _ = Parse.hide "body";

Theorem checked_explicit_external_body_storage_well_formed_on:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP FST args) /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace /\
  eval_stmts cx body st = (res,st') ==>
  storage_well_formed_on cx st' (FST H)
Proof
  strip_tac >>
  drule_all checked_explicit_external_body_setup >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (qpat_x_assum `cx = _` SUBST1_TAC >>
     gvs[checked_contract_runtime_ready_def] >>
     drule_all checked_explicit_external_body_call_evaluation_safe >> simp[]) >>
  irule (cj 2 eval_storage_well_formed_on_mutual) >> simp[] >>
  qexistsl [`env_body`, `env_after`, `res`, `ret`, `body`, `st`] >>
  gvs[runtime_consistent_def]
QED

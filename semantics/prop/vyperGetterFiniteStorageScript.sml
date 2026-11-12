(* Finite storage at the selected public-getter boundary. *)
Theory vyperGetterFiniteStorage
Ancestors
  vyperFiniteStoragePreservation vyperCallFiniteStorageSupport
  vyperTypeContractSoundness vyperInterpreter vyperContext
  vyperTypeCallStackSoundness vyperTypeCallGraph vyperTypeExprSoundness

val _ = Parse.hide "body";

Theorem checked_public_getter_body_storage_well_formed_on:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  module_allocated am.layouts tx.target src ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  eval_stmts cx body st = (res,st') /\
  regions_consistent (FST H) /\
  storage_locks_separated (FST H) (SND H) /\
  storage_well_formed_on cx st (FST H) /\
  storage_observations_ok cx H st'.storage_trace ==>
  storage_well_formed_on cx st' (FST H)
Proof
  strip_tac >>
  drule_all checked_public_getter_post_prefix_body_setup_selected >> strip_tac >>
  `int_calls_stmts body = []` by
    metis_tac[selected_public_getter_body_int_calls_empty] >>
  qmatch_asmsub_abbrev_tac `context_well_typed ecx` >>
  `ecx.txn.target = cx.txn.target` by
    simp[Abbr `ecx`, initial_evaluation_context_def] >>
  `storage_well_formed_on ecx st (FST H)` by
    metis_tac[storage_well_formed_on_target] >>
  `storage_observations_ok ecx H st'.storage_trace` by
    metis_tac[storage_observations_ok_target] >>
  `eval_stmts ecx body st = (res,st')` by metis_tac[] >>
  `call_evaluation_safe ecx []` by (
    `ALOOKUP am.sources tx.target = SOME mods` by
      gvs[checked_contract_runtime_ready_def] >>
    `ecx = ecx with stk := [(src,"")]` by
      simp[Abbr `ecx`, initial_evaluation_context_def, empty_call_txn_def] >>
    pop_assum SUBST1_TAC >>
    irule (INST_TYPE [``:'a`` |-> ``:num``]
      checked_contract_call_evaluation_safe_singleton) >>
    qexistsl [`art`, `am.layouts`, `mods`] >>
    simp[Abbr `ecx`, initial_evaluation_context_def, empty_call_txn_def,
         calls_follow_call_graph_def]) >>
  `storage_well_formed_on ecx st' (FST H)` by (
    irule (cj 2 eval_storage_well_formed_on_mutual) >> simp[] >>
    qexistsl [`function_entry_env art mods src External args`, `env_after`,
              `res`, `ret`, `body`, `st`] >>
    simp[runtime_consistent_def]) >>
  metis_tac[storage_well_formed_on_target]
QED

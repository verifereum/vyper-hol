(* TOP-LEVEL: source account-supply preservation for local and storage operations.
 *)
Theory vyperSourcePrimitiveSupply
Ancestors
  list pair option vyperMisc vyperSourceSupplyDefs vyperSourceOracleSupply
  vyperSupplyBoundary vyperStatePreservation vyperStorageBackend
  vyperInterpreter vyperState vyperPlaceFrames
Libs
  monadsyntax vyperSupplyProofLib

val () = monadsyntax.enable_monad "vyper_evaluation";
val () = Parse.type_abbrev ("exception", ``:vyperState$exception``);

Theorem source_supply_reads:
  source_supply_action (get_place tv) /\
  source_supply_action get_accounts /\
  source_supply_action get_transient_storage /\
  source_supply_action (get_address_immutables cx) /\
  source_supply_action (get_immutables cx src) /\
  source_supply_action (read_result cx tv) /\
  source_supply_action (read_results cx results) /\
  source_supply_action (read_place cx place) /\
  source_supply_action (place_type_value cx place) /\
  source_supply_action (extend_place cx tv subscript) /\
  source_supply_action (select_result cx ann tv subscript) /\
  source_supply_action (conditional_result cx tv) /\
  source_supply_action (lookup_global cx src name) /\
  source_supply_action (lookup_flag_mem cx nsid flag_member) /\
  source_supply_action (read_storage_slot cx transient slot ty) /\
  source_supply_action (get_storage_backend cx transient) /\
  source_supply_action (result_array_length cx tv) /\
  source_supply_action (check test message) /\
  source_supply_action (type_check test message) /\
  source_supply_action (lift_option opt message) /\
  source_supply_action (lift_option_type opt message) /\
  source_supply_action (lift_sum result) /\
  source_supply_action (lift_sum_runtime runtime_result) /\
  source_supply_action (resolve_array_element cx transient slot ty subs)
Proof
  rpt conj_tac >> irule source_supply_action_identity >> rpt strip_tac >> FIRST [
    drule_all get_place_state, drule_all get_accounts_state,
    drule_all get_transient_storage_state, drule_all get_address_immutables_state,
    drule_all get_immutables_state, drule_all read_result_state,
    drule_all read_results_state, drule_all read_place_state,
    drule_all place_type_value_state, drule_all extend_place_state,
    drule_all select_result_state, drule_all conditional_result_state,
    drule_all lookup_global_state, drule_all lookup_flag_mem_state,
    drule_all read_storage_slot_state, drule_all get_storage_backend_state,
    drule_all result_array_length_state,
    drule_all check_state, drule_all type_check_state,
    drule_all lift_option_state, drule_all lift_option_type_state,
    drule_all lift_sum_state, drule_all lift_sum_runtime_state,
    drule_all resolve_array_element_state] >> simp[]
QED

Theorem source_supply_field_updates:
  source_supply_action get_scopes /\
  source_supply_action (set_scopes scope_list) /\
  source_supply_action push_scope /\ source_supply_action pop_scope /\
  source_supply_action (push_scope_with_var name ty value) /\
  source_supply_action (update_transient update) /\
  source_supply_action (append_logs event_list) /\
  source_supply_action (push_log entry_log) /\
  source_supply_action get_pending_deletions /\
  source_supply_action (update_pending_deletions update_pending) /\
  source_supply_action (set_address_immutables cx imms)
Proof
  rpt conj_tac >> irule source_supply_action_exact_frame >>
  rpt gen_tac >> strip_tac >>
  gvs[get_scopes_def, set_scopes_def, push_scope_def, pop_scope_def,
      push_scope_with_var_def, update_transient_def, append_logs_def,
      push_log_def, get_pending_deletions_def, update_pending_deletions_def,
      set_address_immutables_def, return_def, raise_def, AllCaseEqs()]
QED

Theorem source_supply_locals:
  source_supply_action (new_variable name ty value) /\
  source_supply_action (set_variable name value) /\
  source_supply_action (set_immutable cx src name ty value) /\
  source_supply_action (push_function func call_scope cx) /\
  source_supply_action (pop_function scope_list)
Proof
  rpt conj_tac >> irule source_supply_action_exact_frame >>
  rpt gen_tac >> strip_tac >>
  gvs[new_variable_def, set_variable_def, set_immutable_def,
      get_address_immutables_def, set_address_immutables_def,
      get_scopes_def, set_scopes_def, push_function_def, pop_function_def,
      type_check_def, assert_def, lift_option_type_def, bind_def,
      ignore_bind_def, return_def, raise_def, list_CASE_rator,
      option_CASE_rator, prod_CASE_rator, COND_RATOR, AllCaseEqs()] >>
  rename1 `find_containing_scope _ _ = SOME scope_parts` >>
  PairCases_on `scope_parts` >>
  gvs[assert_def, set_scopes_def, bind_def, ignore_bind_def,
      return_def, raise_def, COND_RATOR, AllCaseEqs()]
QED

Theorem source_supply_locks:
  source_supply_action (acquire_nonreentrant_lock address slot is_view) /\
  source_supply_action (release_nonreentrant_lock address slot)
Proof
  rpt conj_tac >> irule source_supply_action_exact_frame >>
  rpt gen_tac >> strip_tac >>
  gvs[acquire_nonreentrant_lock_def, release_nonreentrant_lock_def,
      get_transient_storage_def, update_transient_def,
      bind_def, return_def, raise_def, COND_RATOR, AllCaseEqs()]
QED

Theorem source_supply_set_storage:
  source_supply st ==> source_supply (set_storage cx st transient storage)
Proof
  Cases_on `transient` >> rw[set_storage_def, source_supply_def] >>
  irule (SRULE [vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def]
    accounts_supply_install_same_balance) >> simp[]
QED

Theorem source_supply_action_set_storage_backend:
  source_supply_action (set_storage_backend cx transient storage)
Proof
  simp[source_supply_action_def, set_storage_backend_eq, source_supply_set_storage]
QED

Theorem source_supply_action_write_storage:
  source_supply_action (write_storage_slot cx transient slot ty value)
Proof
  simp[source_supply_action_def] >> gen_tac >> strip_tac >>
  Cases_on `encode_value ty value` >> simp[write_storage_slot_eq] >>
  irule source_supply_set_storage >> simp[]
QED

val source_primitive_facts = List.concat (map (CONJUNCTS o SPEC_ALL)
  [source_supply_reads, source_supply_field_updates, source_supply_locals,
   source_supply_locks, source_supply_action_return, source_supply_action_raise,
   source_supply_action_write_storage, source_supply_action_set_storage_backend]);

val source_primitive_net = vyperSupplyProofLib.fact_net source_primitive_facts
  [source_supply_action_bind_simple, source_supply_action_ignore_bind,
   source_supply_action_cond];

val SOURCE_PRIMITIVE_STEP = FIRST [
  CONV_TAC (HO_REWR_CONV pairTheory.FORALL_PROD), gen_tac,
  first_assum ACCEPT_TAC, vyperSupplyProofLib.solve source_primitive_net,
  CONV_TAC (RAND_CONV (CHANGED_CONV vyperSupplyProofLib.head_conv)),
  strip_tac, conj_tac, vyperSupplyProofLib.case_tac];

Theorem source_supply_action_set_global:
  source_supply_action (set_global cx src name value)
Proof
  simp_tac bool_ss [set_global_def, LET_THM] >> rpt SOURCE_PRIMITIVE_STEP
QED

val () = List.app (fn (n, th) =>
  if List.all (fn s => s = "DISK_THM") (#1 (Tag.dest_tag (Thm.tag th)))
     andalso null (#2 (Tag.dest_tag (Thm.tag th)))
     andalso null (Thm.hyp th)
  then () else raise Fail ("Unexpected proof oracle: " ^ n))
  (DB.thms "vyperSourcePrimitiveSupply");

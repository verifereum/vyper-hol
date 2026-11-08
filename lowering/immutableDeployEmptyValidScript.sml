(* Transaction-valid variant of the shared source fixture. *)
Theory immutableDeployEmptyValid
Ancestors
  immutableDeployEmptyStacked immutableDeployEmptyMachine
  immutableDeployEmptyDeployment bodySim compileEnv vyperContext
  vyperTypeInvariants exprSimHypsDefs vyperTypeCallStackSoundness

Definition empty_immutable_valid_cx_def:
  empty_immutable_valid_cx = empty_immutable_stacked_cx with
    txn := (empty_immutable_stacked_cx.txn with
      <|block_number := 1; block_hashes := [0w]|>)
End

Theorem empty_immutable_valid_tx_env:
  tx_env_ok empty_immutable_valid_cx.txn
Proof
  EVAL_TAC
QED

Theorem empty_immutable_valid_metadata:
  get_module_code empty_immutable_valid_cx src =
    get_module_code empty_immutable_stacked_cx src /\
  get_tenv empty_immutable_valid_cx = get_tenv empty_immutable_stacked_cx /\
  current_module empty_immutable_valid_cx = current_module empty_immutable_stacked_cx /\
  empty_immutable_valid_cx.in_deploy
Proof
  simp[empty_immutable_valid_cx_def, get_module_code_def, get_tenv_def,
       current_module_def, empty_immutable_stacked_cx_def,
       empty_immutable_cx_def]
QED

Theorem empty_immutable_valid_body_inv:
  body_inv empty_immutable_tops empty_immutable_unit.cu_context
    empty_immutable_ce empty_immutable_valid_cx
Proof
  mp_tac empty_immutable_stacked_body_inv >>
  simp[bodySimTheory.body_inv_def, empty_immutable_valid_metadata,
       empty_immutable_stacked_cx_def, empty_immutable_cx_def]
QED

Theorem empty_immutable_valid_env_consistent:
  env_consistent env empty_immutable_valid_cx es <=>
  env_consistent env empty_immutable_stacked_cx es
Proof
  simp[env_consistent_def, env_context_consistent_def,
       env_scopes_consistent_def, env_immutables_consistent_def,
       fn_sigs_consistent_def, fn_sigs_live_def, fn_sigs_declared_complete_def,
       vyperTypeContractTheory.context_function_live_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       empty_immutable_valid_metadata,
       empty_immutable_valid_cx_def, get_module_code_def, get_tenv_def,
       current_module_def, vyperInterpreterTheory.lookup_function_def,
       vyperStateTheory.lookup_var_slot_from_layout_def,
       empty_immutable_stacked_cx_def, empty_immutable_cx_def]
QED

Theorem empty_immutable_valid_functions_typed:
  functions_well_typed empty_immutable_valid_cx
Proof
  mp_tac empty_immutable_stacked_functions_typed >>
  simp[functions_well_typed_def,
       fn_sigs_consistent_def, fn_sigs_live_def, fn_sigs_declared_complete_def,
       vyperTypeContractTheory.context_function_live_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       empty_immutable_valid_metadata, empty_immutable_valid_cx_def,
       get_module_code_def, get_tenv_def,
       vyperStateTheory.lookup_var_slot_from_layout_def,
       empty_immutable_stacked_cx_def, empty_immutable_cx_def]
QED

Theorem empty_immutable_valid_context_typed:
  context_well_typed empty_immutable_valid_cx
Proof
  EVAL_TAC
QED


Theorem empty_immutable_valid_storage_backend:
  !b. get_storage_backend empty_immutable_valid_cx b =
      get_storage_backend empty_immutable_stacked_cx b
Proof
  Cases >> simp[vyperStateTheory.get_storage_backend_def,
                empty_immutable_valid_cx_def]
QED

Theorem empty_immutable_valid_declared_region:
  declared_storage_region empty_immutable_valid_cx mid n subs =
  declared_storage_region empty_immutable_stacked_cx mid n subs
Proof
  simp[vyperStorageLayoutSafetyTheory.declared_storage_region_def,
       empty_immutable_valid_metadata,
       vyperStateTheory.lookup_var_slot_from_layout_def,
       empty_immutable_valid_cx_def]
QED

Theorem empty_immutable_valid_storage_var_info:
  storage_var_info empty_immutable_valid_cx mid n =
  storage_var_info empty_immutable_stacked_cx mid n
Proof
  simp[vyperLookupStorageTheory.storage_var_info_def,
       empty_immutable_valid_metadata,
       vyperStateTheory.lookup_var_slot_from_layout_def,
       empty_immutable_valid_cx_def]
QED

Theorem empty_immutable_valid_storage_well_formed:
  contract_storage_well_formed empty_immutable_valid_cx st <=>
  contract_storage_well_formed empty_immutable_stacked_cx st
Proof
  simp[vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       empty_immutable_valid_storage_backend,
       empty_immutable_valid_declared_region,
       empty_immutable_valid_storage_var_info]
QED

Theorem empty_immutable_valid_layout_safe:
  storage_layout_safe empty_immutable_valid_cx <=>
  storage_layout_safe empty_immutable_stacked_cx
Proof
  simp[vyperStorageLayoutSafetyTheory.storage_layout_safe_def,
       vyperLookupStorageTheory.well_formed_layout_def,
       empty_immutable_valid_declared_region,
       empty_immutable_valid_storage_var_info,
       vyperStorageLayoutSafetyTheory.nonreentrant_slot_separated_def,
       empty_immutable_valid_cx_def]
QED

Theorem empty_immutable_valid_oracle_storage:
  oracle_storage_ok empty_immutable_valid_cx st <=>
  oracle_storage_ok empty_immutable_stacked_cx st
Proof
  simp[vyperTypeStoragePreservationTheory.oracle_storage_ok_def,
       empty_immutable_valid_storage_well_formed]
QED

Theorem empty_immutable_valid_bare_layout:
  bare_globals_layout ctor types vars empty_immutable_valid_cx globals assignable <=>
  bare_globals_layout ctor types vars empty_immutable_stacked_cx globals assignable
Proof
  simp[bare_globals_layout_def, empty_immutable_valid_metadata,
       empty_immutable_valid_cx_def, empty_immutable_stacked_cx_def,
       empty_immutable_cx_def]
QED

Theorem empty_immutable_valid_sim_inv:
  expr_sim_inv empty_immutable_ce empty_immutable_valid_cx empty_immutable_env
    empty_immutable_es
Proof
  mp_tac empty_immutable_stacked_sim_inv >>
  simp[expr_sim_inv_def, empty_immutable_valid_env_consistent,
       empty_immutable_valid_functions_typed, empty_immutable_valid_context_typed,
       empty_immutable_stacked_functions_typed, empty_immutable_stacked_state_typed,
       empty_immutable_valid_metadata, empty_immutable_valid_storage_well_formed,
       empty_immutable_valid_layout_safe, empty_immutable_valid_oracle_storage,
       empty_immutable_valid_bare_layout] >>
  metis_tac[]
QED

Theorem empty_immutable_valid_calls_safe:
  call_evaluation_safe empty_immutable_valid_cx
    (int_calls_expr empty_immutable_expr)
Proof
  mp_tac empty_immutable_stacked_calls_safe >>
  simp[call_evaluation_safe_def,
       vyperTypeCallStackSoundnessTheory.functions_follow_call_graph_def,
       vyperInterpreterTheory.lookup_function_def,
       empty_immutable_valid_cx_def, get_module_code_def, get_tenv_def]
QED

Theorem empty_immutable_valid_body_pre:
  expr_body_pre empty_immutable_ce empty_immutable_valid_cx empty_immutable_env
    empty_immutable_expr empty_immutable_es
Proof
  mp_tac empty_immutable_stacked_body_pre >>
  simp[expr_body_pre_def, empty_immutable_valid_sim_inv,
       empty_immutable_stacked_sim_inv, empty_immutable_valid_calls_safe,
       empty_immutable_stacked_calls_safe,
       gasContextTheory.cx_tops_def, empty_immutable_valid_metadata]
QED

Theorem empty_immutable_valid_vv_sim:
  !ctx func ty.
    expr_vv_sim ctx func empty_immutable_ce empty_immutable_valid_cx ty
      empty_immutable_expr empty_immutable_es
Proof
  rpt gen_tac >> mp_tac empty_immutable_valid_body_pre >>
  simp[immutableDeployEmptySourceTheory.empty_immutable_expr_def] >>
  metis_tac[immutableDeployEmptyFixtureTheory.empty_struct_vv_sim]
QED

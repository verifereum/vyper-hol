Theory exprSimAbiDecodeRealizeTarget
Ancestors
  exprSimAbiDecodeRealizeSource exprSimHyps exprSimLeaves exprSimHypsDefs
  exprLoweringProps compileEnv vyperContext vyperTypeInvariants vyperInterpreter
  vyperTypeInitialState vyperTypeSystem vyperValue vyperState
  exprSimAbiDecodeSizeProbe exprSimAbiDecodeGuardProbe supportedProgram exprLowering

Theorem abi_decode_realize_child:
  exprs_case T ctx func ce cx [abi_decode_realize_arg]
Proof
  irule exprs_case_every_ok >>
  simp[abi_decode_realize_arg_def, compile_literal_case_sim]
QED

(* The source-only witness used the empty transaction.  The full simulation
   requires a nonzero block number independently of the decoder fragment. *)
Theorem abi_decode_realize_entry_excluded:
  ~stmt_state_rel ctx func ce (abi_decode_realize_cx k) es ss
Proof
  simp[stmt_state_rel_def, compileEnvTheory.state_rel_def,
       compileEnvTheory.call_ctx_rel_def, compileEnvTheory.tx_env_ok_def,
       abi_decode_realize_cx_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def]
QED

Definition abi_decode_realize_txn_def:
  abi_decode_realize_txn = empty_call_txn with
    <|block_number := 1; block_hashes := [0w]|>
End

Definition abi_decode_realize_live_cx_def:
  abi_decode_realize_live_cx k = (abi_decode_realize_cx k) with
    txn := abi_decode_realize_txn
End

Theorem abi_decode_realize_txn_ok:
  tx_env_ok abi_decode_realize_txn
Proof
  simp[tx_env_ok_def, abi_decode_realize_txn_def,
       vyperContextTheory.empty_call_txn_def]
QED

Theorem abi_decode_realize_live_interfaces:
  get_module_code (abi_decode_realize_live_cx k) src =
    get_module_code (abi_decode_realize_cx k) src /\
  get_tenv (abi_decode_realize_live_cx k) = get_tenv (abi_decode_realize_cx k) /\
  gasContext$cx_tops (abi_decode_realize_live_cx k) =
    gasContext$cx_tops (abi_decode_realize_cx k) /\
  functions_well_typed (abi_decode_realize_live_cx k) /\
  call_evaluation_safe (abi_decode_realize_live_cx k) []
Proof
  simp[abi_decode_realize_live_cx_def, abi_decode_realize_txn_def,
       abi_decode_realize_cx_def, vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.get_module_code_def, vyperContextTheory.get_tenv_def,
       gasContextTheory.cx_tops_def,
       vyperTypeInvariantsTheory.functions_well_typed_def,
       abi_decode_realize_tops_def,
       vyperInterpreterTheory.lookup_callable_function_def,
       vyperInterpreterTheory.lookup_function_def] >>
  rewrite_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
  qexistsl_tac [`[]`, `(NONE,"probe")`, `[]`] >>
  simp[vyperTypeCallStackSoundnessTheory.call_stack_follows_def,
       vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_def,
       vyperTypeCallStackSoundnessTheory.functions_follow_call_graph_def,
       vyperContextTheory.get_module_code_def, abi_decode_realize_tops_def,
       vyperInterpreterTheory.lookup_callable_function_def,
       vyperInterpreterTheory.lookup_function_def] >>
  simp[relationTheory.irreflexive_def] >> gen_tac >> strip_tac >>
  pop_assum mp_tac >> simp[Once relationTheory.TC_CASES1,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED

Theorem abi_decode_realize_live_env_consistent:
  env_consistent abi_decode_realize_env (abi_decode_realize_live_cx k)
    abi_decode_realize_state
Proof
  simp[abi_decode_realize_live_cx_def, abi_decode_realize_txn_def,
       abi_decode_realize_env_def, abi_decode_realize_state_def,
       initial_state_def, initial_machine_state_def,
       abi_decode_realize_cx_def, empty_evaluation_context_def,
       empty_call_txn_def, get_tenv_def, type_env_all_modules_def,
       type_env_for_module_def, abi_decode_realize_tops_def,
       get_module_code_def, current_module_def,
       env_consistent_def, env_context_consistent_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       env_scopes_consistent_def, env_immutables_consistent_def,
       fn_sigs_consistent_def, fn_sigs_declared_complete_def,
       fn_sigs_live_def, vyperStateTheory.lookup_scopes_def, lookup_flag_def]
QED

Theorem abi_decode_realize_live_inv:
  expr_sim_inv (abi_decode_realize_ce ce) (abi_decode_realize_live_cx k)
    abi_decode_realize_env abi_decode_realize_state
Proof
  simp[expr_sim_inv_def, abi_decode_realize_live_env_consistent,
       abi_decode_realize_live_interfaces, abi_decode_realize_tenv,
       abi_decode_realize_ce_def, abi_decode_realize_env_def,
       abi_decode_realize_state_def, initial_state_def, initial_machine_state_def,
       state_well_typed_def, scope_well_typed_def,
       accounts_well_typed_def, account_well_typed_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
       vfmStateTheory.empty_account_state_def,
       context_well_typed_def, abi_decode_realize_live_cx_def,
       abi_decode_realize_txn_def, abi_decode_realize_cx_def,
       empty_evaluation_context_def, empty_call_txn_def,
       get_module_code_def, abi_decode_realize_tops_def, lookup_flag_def,
       sfields_tenv_consistent_def, outcomes_accounts_typed_def,
       popped_keys_indexed_def,
       placeTypingPropsTheory.place_map_tables_agree_on_defined_def,
       find_var_decl_by_name_def,
       vyperTypeStoragePreservationTheory.oracle_storage_ok_def,
       vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def,
       vyperStorageLayoutSafetyTheory.storage_layout_safe_def,
       vyperStorageLayoutSafetyTheory.nonreentrant_slot_separated_def,
       vyperStorageLayoutSafetyTheory.declared_storage_region_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.well_formed_layout_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       vyperLookupStorageTheory.storage_var_info_def] >>
  rpt conj_tac >> rpt gen_tac >>
  rpt IF_CASES_TAC >> simp[find_var_decl_by_name_def]
QED

Theorem abi_decode_realize_live_body_pre:
  expr_body_pre (abi_decode_realize_ce ce) (abi_decode_realize_live_cx k)
    abi_decode_realize_env (abi_decode_realize_expr k) abi_decode_realize_state
Proof
  simp[expr_body_pre_def, abi_decode_realize_live_inv, abi_decode_realize_typed,
       abi_decode_realize_alloc, abi_decode_realize_no_calls,
       abi_decode_realize_live_interfaces, abi_decode_realize_occurs,
       abi_decode_realize_tenv] >>
  simp[abi_decode_realize_expr_def, abi_decode_realize_arg_def,
       byte_widths_expr_def, supportedExprTraverseTheory.expr_has_evm_run_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_evm_run_root_def, type_bits_def] >>
  Cases_on `k` >> simp[abi_decode_size_probe_type_def, type_bits_def]
QED

Theorem abi_decode_realize_live_eval:
  ?v. !es. eval_expr (abi_decode_realize_live_cx k) (abi_decode_realize_expr k) es =
    (INL (Value v), es)
Proof
  `?v. evaluate_abi_decode FEMPTY (abi_decode_size_probe_type k)
    (REPLICATE 32 0w) = INL v` by
    metis_tac[abi_decode_guard_probe_source_zero] >>
  pop_assum strip_assume_tac >> qexists_tac `v` >>
  simp[abi_decode_realize_expr_def, abi_decode_realize_arg_def,
       Once vyperInterpreterTheory.evaluate_def, evaluate_type_builtin_def,
       vyperASTTheory.expr_type_def] >>
  simp[type_builtin_args_length_ok_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def] >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  simp[Once vyperInterpreterTheory.evaluate_def, bind_def, return_def,
       vyperValueOperationTheory.evaluate_literal_def, read_result_def, lift_sum_def,
       evaluate_type_builtin_def, abi_decode_realize_live_interfaces,
       abi_decode_realize_tenv] >>
  simp[Once vyperInterpreterTheory.evaluate_def, return_def,
       evaluate_type_builtin_def, abi_decode_realize_live_interfaces,
       abi_decode_realize_tenv, lift_sum_def]
QED

Theorem abi_decode_realize_live_admissible:
  gas_admissible
    (eval_expr (abi_decode_realize_live_cx k) (abi_decode_realize_expr k))
    expr_vv_res_ok es
Proof
  strip_assume_tac abi_decode_realize_live_eval >>
  simp[gasContextTheory.gas_admissible_def,
       exprSimDefsTheory.expr_vv_res_ok_def]
QED

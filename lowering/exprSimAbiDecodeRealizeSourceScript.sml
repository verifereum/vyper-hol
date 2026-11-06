Theory exprSimAbiDecodeRealizeSource
Ancestors
  exprSimAbiDecodeGuardProbe exprSimHypsDefs vyperTypeInitialState
  supportedProgram exprLowering compileEnv list exprSimAbiDecodeSizeProbe
  vyperTypeSystem vyperValue vyperContext vyperInterpreter vyperTypeInvariants
  vyperState

Definition abi_decode_realize_arg_def:
  abi_decode_realize_arg =
    Literal (BaseT (BytesT (Dynamic 32))) (BytesL (REPLICATE 32 0w))
End

Definition abi_decode_realize_expr_def:
  abi_decode_realize_expr k =
    TypeBuiltin (abi_decode_size_probe_type k) (AbiDecode F)
      (abi_decode_size_probe_type k) [abi_decode_realize_arg]
End

Theorem abi_decode_realize_no_calls:
  int_calls_expr (abi_decode_realize_expr k) = []
Proof
  simp[abi_decode_realize_expr_def, abi_decode_realize_arg_def,
       vyperTypeCallGraphTheory.int_calls_expr_def]
QED

Theorem abi_decode_realize_assignable:
  !k. assignable_type env (abi_decode_size_probe_type k)
Proof
  Induct
  >- (EVAL_TAC >> simp[wordsTheory.dimword_def]) >>
  simp[abi_decode_size_probe_type_def, Once assignable_type_def] >>
  drule assignable_type_well_formed >>
  simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  drule abiCallerDecodeBoundsTheory.abi_caller_singleton_type >>
  metis_tac[]
QED

Theorem abi_decode_realize_widths:
  !k. abi_decode_bytes_widths env (abi_decode_size_probe_type k)
Proof
  Induct >> simp[abi_decode_size_probe_type_def, abi_decode_bytes_widths_def]
QED

Theorem abi_decode_realize_alloc:
  alloc_limits_expr ce (abi_decode_realize_expr k)
Proof
  simp[abi_decode_realize_expr_def, abi_decode_realize_arg_def,
    allocLimitsTheory.alloc_limits_expr_def, allocLimitsTheory.type_alloc_ok_def,
    allocLimitsTheory.literal_alloc_ok_def, abi_decode_size_probe_memory,
    compileEnvTheory.type_memory_bytes_def] >>
  EVAL_TAC
QED

Theorem abi_decode_realize_arg_typed:
  well_typed_expr env abi_decode_realize_arg
Proof
  simp[abi_decode_realize_arg_def, well_typed_expr_def,
       well_typed_literal_def, well_formed_type_def, evaluate_type_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem abi_decode_realize_typed:
  well_typed_expr env (abi_decode_realize_expr k)
Proof
  simp[abi_decode_realize_expr_def, Once well_typed_expr_def,
       type_builtin_result_ok_def, well_typed_type_builtin_args_def,
       abi_decode_realize_assignable, abi_decode_realize_widths,
       abi_decode_realize_arg_typed, abi_decode_realize_arg_def,
       vyperASTTheory.expr_type_def] >>
  conj_tac
  >- (rewrite_tac[GSYM abi_decode_realize_arg_def] >>
      simp[well_typed_expr_def, abi_decode_realize_arg_typed]) >>
  metis_tac[abi_decode_realize_assignable, assignable_type_well_formed]
QED

Definition abi_decode_realize_tops_def:
  abi_decode_realize_tops k =
    [FunctionDecl External Pure F F "probe" [] [] NoneT
      [Expr (abi_decode_realize_expr k)]]
End

Definition abi_decode_realize_cx_def:
  abi_decode_realize_cx k = empty_evaluation_context with
    <|stk := [(NONE, "probe")];
      sources := [(empty_call_txn.target, [(NONE, abi_decode_realize_tops k)])]|>
End

Definition abi_decode_realize_env_def:
  abi_decode_realize_env =
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
       flag_members := FEMPTY; event_fields := FEMPTY |>
End

Definition abi_decode_realize_state_def:
  abi_decode_realize_state =
    (initial_state initial_machine_state [FEMPTY]) with outcomes := SOME []
End

Theorem abi_decode_realize_module:
  get_module_code (abi_decode_realize_cx k) src =
    if src = NONE then SOME (abi_decode_realize_tops k) else NONE
Proof
  simp[abi_decode_realize_cx_def, empty_evaluation_context_def,
       get_module_code_def]
QED

Theorem abi_decode_realize_functions:
  functions_well_typed (abi_decode_realize_cx k)
Proof
  simp[functions_well_typed_def, abi_decode_realize_module] >>
  rpt strip_tac >> gvs[] >>
  gvs[abi_decode_realize_cx_def, empty_evaluation_context_def,
      abi_decode_realize_tops_def, lookup_callable_function_def,
      lookup_function_def]
QED

Theorem abi_decode_realize_tenv:
  get_tenv (abi_decode_realize_cx k) = FEMPTY /\
  type_env (gasContext$cx_tops (abi_decode_realize_cx k)) = FEMPTY
Proof
  simp[get_tenv_def, abi_decode_realize_cx_def,
       empty_evaluation_context_def, type_env_all_modules_def,
       type_env_for_module_def, abi_decode_realize_tops_def,
       gasContextTheory.cx_tops_def, get_module_code_def, type_env_def]
QED

Theorem abi_decode_realize_occurs:
  supported_expr_exists (expr_abi_decode_target_root target)
    (abi_decode_realize_expr k) ==>
  occurs_abi_decode_target target (gasContext$cx_tops (abi_decode_realize_cx k))
Proof
  simp[gasContextTheory.cx_tops_def, abi_decode_realize_module,
       abi_decode_realize_tops_def, occurs_abi_decode_target_function,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedStmtTraverseTheory.supported_stmt_expr_exists_def]
QED

Theorem abi_decode_realize_env_consistent:
  env_consistent abi_decode_realize_env (abi_decode_realize_cx k)
    abi_decode_realize_state
Proof
  simp[abi_decode_realize_env_def, abi_decode_realize_state_def,
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

Definition abi_decode_realize_ce_def:
  abi_decode_realize_ce (ce : compile_env) = ce with ce_struct_fields := FEMPTY
End

Theorem abi_decode_realize_inv:
  expr_sim_inv (abi_decode_realize_ce ce) (abi_decode_realize_cx k)
    abi_decode_realize_env abi_decode_realize_state
Proof
  simp[expr_sim_inv_def, abi_decode_realize_env_consistent,
       abi_decode_realize_functions, abi_decode_realize_tenv,
       abi_decode_realize_ce_def, abi_decode_realize_env_def,
       abi_decode_realize_state_def, initial_state_def, initial_machine_state_def,
       state_well_typed_def, scope_well_typed_def,
       accounts_well_typed_def, account_well_typed_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
       vfmStateTheory.empty_account_state_def,
       context_well_typed_def, abi_decode_realize_cx_def,
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

Theorem abi_decode_realize_call_safe:
  call_evaluation_safe (abi_decode_realize_cx k) []
Proof
  rewrite_tac[vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def] >>
  qexistsl_tac [`[]`, `(NONE,"probe")`, `[]`] >>
  simp[abi_decode_realize_cx_def, empty_evaluation_context_def,
       vyperTypeCallStackSoundnessTheory.call_stack_follows_def,
       vyperTypeCallStackSoundnessTheory.calls_follow_call_graph_def,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def] >>
  simp[vyperTypeCallStackSoundnessTheory.functions_follow_call_graph_def,
       get_module_code_def, abi_decode_realize_tops_def,
       lookup_callable_function_def, lookup_function_def] >>
  simp[relationTheory.irreflexive_def] >>
  gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  simp[Once relationTheory.TC_CASES1,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED

Theorem abi_decode_realize_body_pre:
  expr_body_pre (abi_decode_realize_ce ce) (abi_decode_realize_cx k)
    abi_decode_realize_env (abi_decode_realize_expr k) abi_decode_realize_state
Proof
  simp[expr_body_pre_def, abi_decode_realize_inv, abi_decode_realize_typed,
       abi_decode_realize_alloc, abi_decode_realize_no_calls,
       abi_decode_realize_occurs, abi_decode_realize_tenv,
       abi_decode_realize_call_safe] >>
  simp[abi_decode_realize_expr_def, abi_decode_realize_arg_def,
       byte_widths_expr_def, supportedExprTraverseTheory.expr_has_evm_run_def,
       vyperTypeCallStackSoundnessTheory.call_evaluation_safe_def,
       supportedExprTraverseTheory.supported_expr_exists_def,
       supportedExprTraverseTheory.expr_evm_run_root_def, type_bits_def] >>
  Cases_on `k` >> simp[abi_decode_size_probe_type_def, type_bits_def]
QED

Theorem abi_decode_realize_eval:
  ?v. !es. eval_expr (abi_decode_realize_cx k) (abi_decode_realize_expr k) es =
    (INL (Value v), es)
Proof
  `?v. evaluate_abi_decode FEMPTY (abi_decode_size_probe_type k)
    (REPLICATE 32 0w) = INL v` by
    metis_tac[abi_decode_guard_probe_source_zero] >>
  pop_assum strip_assume_tac >>
  qexists_tac `v` >>
  simp[abi_decode_realize_expr_def, abi_decode_realize_arg_def,
       Once vyperInterpreterTheory.evaluate_def, evaluate_type_builtin_def,
       vyperASTTheory.expr_type_def] >>
  simp[type_builtin_args_length_ok_def, type_check_def, assert_def,
       ignore_bind_def, bind_def, return_def] >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  simp[Once vyperInterpreterTheory.evaluate_def, bind_def, return_def,
       vyperValueOperationTheory.evaluate_literal_def, read_result_def, lift_sum_def,
       evaluate_type_builtin_def, abi_decode_realize_tenv] >>
  simp[Once vyperInterpreterTheory.evaluate_def, return_def,
       evaluate_type_builtin_def, abi_decode_realize_tenv, lift_sum_def]
QED

Theorem abi_decode_realize_admissible:
  gas_admissible
    (eval_expr (abi_decode_realize_cx k) (abi_decode_realize_expr k))
    expr_vv_res_ok es
Proof
  strip_assume_tac abi_decode_realize_eval >>
  simp[gasContextTheory.gas_admissible_def,
       exprSimDefsTheory.expr_vv_res_ok_def]
QED

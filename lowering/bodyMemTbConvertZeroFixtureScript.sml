(* Empty-unit feasibility for the zero-capacity convert probe. *)
Theory bodyMemTbConvertZeroFixture
Ancestors
  bodyMemTbConvertZeroProbe compileVyper venomCompilerTypes venomPolicyTypes
  vyperTypeInvariants vyperState vyperContext vyperTypeCallStackSoundness
  vyperStorageLayoutSafety vyperLookupStorage exprSimHypsDefs compileEnv placeTypingProps
  vyperTypeStoragePreservation

Theorem convert_zero_empty_unit_exists:
  IS_SOME (lower_vyper_runtime_unit []
    <| rpol_target := all_capabilities;
       rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> )
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem convert_zero_source_state_typed:
  state_well_typed
    (empty_state with <| outcomes := SOME []; scopes := [FEMPTY] |> )
Proof
  simp[state_well_typed_def, scope_well_typed_def, empty_state_def]
QED

Theorem convert_zero_context_typed:
  context_well_typed
    (empty_evaluation_context with
      <| sources := [(0w, [(NONE, [])])]; stk := [(NONE, "")] |> )
Proof
  EVAL_TAC
QED

Theorem convert_zero_context_functions_typed:
  functions_well_typed
    (empty_evaluation_context with
      <| sources := [(0w, [(NONE, [])])]; stk := [(NONE, "")] |> )
Proof
  simp[functions_well_typed_def, get_module_code_def,
       empty_evaluation_context_def, empty_call_txn_def,
       vyperInterpreterTheory.lookup_callable_function_def,
       vyperInterpreterTheory.lookup_function_def]
QED

Theorem convert_zero_context_calls_safe:
  call_evaluation_safe
    (empty_evaluation_context with
      <| sources := [(0w, [(NONE, [])])]; stk := [(NONE, "")] |> ) []
Proof
  simp[call_evaluation_safe_def, empty_evaluation_context_def] >>
  qexists_tac `[]` >>
  simp[call_stack_follows_def, functions_follow_call_graph_def,
       get_module_code_def, empty_call_txn_def,
       vyperInterpreterTheory.lookup_callable_function_def,
       vyperInterpreterTheory.lookup_function_def,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
       relationTheory.irreflexive_def] >>
  `!x y : num option # string. (call_edge_rel [])^+ x y ==> F` suffices_by metis_tac[] >>
  ho_match_mp_tac relationTheory.TC_INDUCT >>
  simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED

Theorem convert_zero_environment_consistent:
  env_consistent
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
       flag_members := FEMPTY; event_fields := FEMPTY |>
    (empty_evaluation_context with
      <| sources := [(0w, [(NONE, [])])]; stk := [(NONE, "")] |> )
    (empty_state with <| outcomes := SOME []; scopes := [FEMPTY] |> )
Proof
  simp[env_consistent_def, env_context_consistent_def,
       env_scopes_consistent_def, env_immutables_consistent_def,
       empty_state_def, fn_sigs_consistent_def, fn_sigs_live_def,
       fn_sigs_declared_complete_def, toplevel_vtypes_complete_def,
       bare_globals_complete_def, bare_global_assignable_complete_def,
       flag_members_complete_def, empty_evaluation_context_def,
       empty_call_txn_def, current_module_def, get_module_code_def,
       vyperStateTheory.lookup_scopes_def] >>
  EVAL_TAC >> simp[]
QED

Theorem convert_zero_source_accounts_typed:
  accounts_well_typed empty_state.accounts
Proof
  rewrite_tac[accounts_well_typed_def, account_well_typed_def] >>
  gen_tac >> EVAL_TAC
QED

Theorem convert_zero_storage_invariants:
  storage_layout_safe
    (empty_evaluation_context with
      <| sources := [(0w, [(NONE, [])])]; stk := [(NONE, "")] |> ) /\
  contract_storage_well_formed
    (empty_evaluation_context with
      <| sources := [(0w, [(NONE, [])])]; stk := [(NONE, "")] |> )
    (empty_state with <| outcomes := SOME []; scopes := [FEMPTY] |> )
Proof
  simp[storage_layout_safe_def, contract_storage_well_formed_def,
       well_formed_layout_def, well_formed_storage_def,
       storage_var_in_range_def, storage_var_info_def,
       declared_storage_region_def, nonreentrant_slot_separated_def,
       empty_evaluation_context_def, empty_call_txn_def, get_module_code_def,
       vyperStateTheory.find_var_decl_by_name_def,
       SF boolSimps.COND_elim_ss]
QED

Theorem convert_zero_expr_invariant:
  !cenv. cenv.ce_struct_fields = FEMPTY ==>
  expr_sim_inv cenv
    (empty_evaluation_context with
      <| sources := [(0w, [(NONE, [])])]; stk := [(NONE, "")] |> )
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
       flag_members := FEMPTY; event_fields := FEMPTY |>
    (empty_state with <| outcomes := SOME []; scopes := [FEMPTY] |> )
Proof
  rpt strip_tac >>
  simp[expr_sim_inv_def, convert_zero_environment_consistent,
       convert_zero_source_state_typed, convert_zero_context_typed,
       convert_zero_context_functions_typed, convert_zero_storage_invariants,
       accounts_well_typed_def, account_well_typed_def,
       outcomes_accounts_typed_def, oracle_storage_ok_def,
       popped_keys_indexed_def, place_map_tables_agree_on_defined_def,
       sfields_tenv_consistent_def, empty_state_def,
       get_module_code_def, empty_evaluation_context_def, empty_call_txn_def,
       vyperStateTheory.find_var_decl_by_name_def, SF boolSimps.COND_elim_ss] >>
  EVAL_TAC >> simp[]
QED

(* Empty-unit feasibility for the zero-capacity convert probe. *)
Theory bodyMemTbConvertZeroFixture
Ancestors
  bodyMemTbConvertZeroProbe compileVyper venomCompilerTypes venomPolicyTypes
  vyperTypeInvariants vyperState vyperContext vyperTypeCallStackSoundness
  vyperStorageLayoutSafety vyperLookupStorage exprSimHypsDefs compileEnv placeTypingProps
  vyperTypeStoragePreservation bodySim bodyMemoryPreds bodyLiteralBufferMemory

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

Theorem convert_zero_body_environment_exists:
  ?ctx cenv.
    body_inv [] ctx cenv
      (empty_evaluation_context with
        <| sources := [(0w, [(NONE, [])])]; stk := [(NONE, "")] |> ) /\
    cenv.ce_struct_fields = FEMPTY
Proof
  qexistsl_tac
    [`(THE (lower_vyper_runtime_unit []
       <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
          rpol_final_assembly := FAP_Optimize |>)).cu_context`,
     `(ARB : compile_env) with
       <| ce_target := all_capabilities;
          ce_func_ids := build_func_ids 0 [];
          ce_func_param_types := build_func_param_types [];
          ce_func_info := build_func_info (get_struct_fields (make_struct_fields_map [])) [];
          ce_func_return_type := build_func_return_type [];
          ce_event_info := build_event_info (type_env []) [] (K NONE);
          ce_struct_fields := make_struct_fields_map [];
          ce_is_ctor := F; ce_alloca_locals := T;
          ce_hashmap_info := build_hashmap_info [];
          ce_module_dynarray_capacity := build_dynarray_capacity (collect_module_vars []);
          ce_module_var_type := build_var_type_map [] |> `] >>
  simp[body_inv_def, empty_evaluation_context_def, empty_call_txn_def,
       get_module_code_def] >>
  simp[compileVyperTheory.make_struct_fields_map_def,
       typedCopyDomainTheory.acyclic_struct_metadata_def] >>
  reverse conj_tac >- EVAL_TAC >>
  conj_tac >- EVAL_TAC >>
  reverse conj_tac >- (EVAL_TAC >> simp[]) >>
  qexistsl_tac
    [`<| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
          rpol_final_assembly := FAP_Optimize |>`,
     `THE (lower_vyper_runtime_unit []
       <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
          rpol_final_assembly := FAP_Optimize |>)`] >>
  mp_tac convert_zero_empty_unit_exists >>
  Cases_on `lower_vyper_runtime_unit []
       <| rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
          rpol_final_assembly := FAP_Optimize |>` >> simp[]
QED

Theorem convert_zero_body_pre:
  !cenv. cenv.ce_struct_fields = FEMPTY ==>
  expr_body_pre cenv
    (empty_evaluation_context with
      <| sources := [(0w, [(NONE, [])])]; stk := [(NONE, "")] |> )
    <| current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
       bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
       toplevel_vtypes := FEMPTY; type_defs := FEMPTY; fn_sigs := FEMPTY;
       flag_members := FEMPTY; event_fields := FEMPTY |>
    (TypeBuiltin (BaseT BoolT) Convert (BaseT BoolT)
      [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])])
    (empty_state with <| outcomes := SOME []; scopes := [FEMPTY] |> )
Proof
  rpt strip_tac >>
  simp[expr_body_pre_def, convert_zero_expr_invariant,
       convert_zero_literal_static_pre,
       vyperTypeCallGraphTheory.int_calls_expr_def,
       convert_zero_context_calls_safe] >>
  mp_tac convert_zero_context_calls_safe >>
  EVAL_TAC >> simp[]
QED

Theorem convert_zero_operand_induction_hypothesis:
  !cx. body_exprs_mem_ok cx
    [Literal (BaseT (BytesT (Dynamic 0))) (BytesL [])]
Proof
  simp[body_exprs_mem_ok_def, body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  irule literal_other_body_mem >>
  simp[expr_sim_pre_def, expr_body_pre_def,
       vyperTypeCallGraphTheory.int_calls_expr_def,
       compileEnvTheory.is_word_type_def] >>
  gvs[expr_body_pre_def] >>
  qexists_tac `env` >>
  gvs[vyperTypeCallGraphTheory.int_calls_expr_def]
QED

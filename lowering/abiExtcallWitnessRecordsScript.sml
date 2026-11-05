(* Concrete records for testing the full extcall witness preconditions. *)
Theory abiExtcallWitnessRecords
Ancestors
  abiExtcallWitnessProbe vyperTypeInvariants vyperTypeContract gasContext
  vyperContext vyperState

Definition witness_cx_def:
  witness_cx = empty_evaluation_context with
    <|txn := empty_call_txn with <|block_number := 1; block_hashes := [0w]|>;
      sources := [(0w,[(NONE,[])])]; layouts := [(0w,([],[]))]|>
End

Definition witness_env_def:
  witness_env = artifact_env empty_contract_type_artifact [(NONE,[])] NONE
End

Definition witness_es_def:
  witness_es = empty_state with <|scopes := [FEMPTY]; outcomes := SOME [reach_outcome]|>
End

Definition witness_s0_def:
  witness_s0 = init_venom_state "entry" with
    <|vs_outcomes := [reach_outcome];
      vs_block_ctx := (empty_block_context with
        <|bc_number := 1w; bc_blockhash := (\_. 0w)|>)|>
End

Definition witness_cenv_def:
  witness_cenv : compile_env =
    <|ce_target := (\_. T); ce_vars := FEMPTY; ce_module_vars := FEMPTY;
      ce_storage_layout := FEMPTY; ce_module := NONE; ce_struct_fields := FEMPTY;
      ce_dynarray_capacity := (\_.0); ce_module_dynarray_capacity := (\_.0);
      ce_method_id := (\name tys. w2n (calldata_method_id
        (function_selector name (vyper_to_abi_types FEMPTY tys))));
      ce_flag_member_id := (\_ _.0); ce_flag_n_members := (\_.0);
      ce_var_type := (\_.NONE); ce_module_var_type := (\_.NONE);
      ce_hashmap_info := (\_.NONE); ce_event_info := (\_.NONE);
      ce_type_env := FEMPTY; ce_returns_count := 0; ce_return_buf := NONE;
      ce_return_pc := NONE; ce_ctor_exit_label := NONE; ce_is_external := F;
      ce_max_return_size := 0; ce_ret_enc_info := AbiPrimWord;
      ce_ret_dec_info := DecPrimWord NoClamp; ce_is_ctor := F;
      ce_imm_alloca := NONE; ce_func_info := (\_.(0,0,[]));
      ce_func_param_types := (\_.[]); ce_func_return_type := (\_.NoneT);
      ce_func_ids := (\_.0); ce_nonreentrant := (F,0,F,F);
      ce_raw_return := F; ce_alloca_locals := F|>
End

Theorem witness_context_typed:
  context_well_typed witness_cx
Proof
  simp[context_well_typed_def, witness_cx_def, empty_evaluation_context_def,
       empty_call_txn_def]
QED

Theorem witness_state_typed:
  state_well_typed witness_es
Proof
  simp[state_well_typed_def, scope_well_typed_def, witness_es_def, empty_state_def]
QED

Theorem witness_tops:
  cx_tops witness_cx = []
Proof
  EVAL_TAC
QED

Theorem witness_tenv:
  get_tenv witness_cx = FEMPTY
Proof
  EVAL_TAC >> simp[]
QED

Theorem witness_accounts_typed:
  accounts_well_typed witness_es.accounts
Proof
  rewrite_tac[accounts_well_typed_def] >> gen_tac >> EVAL_TAC
QED

(* env_scopes_consistent requires a nonempty stack, even with no locals. *)
Theorem witness_scopes_consistent:
  env_scopes_consistent witness_env witness_cx witness_es
Proof
  EVAL_TAC >> simp[]
QED

Theorem witness_immutables_consistent:
  env_immutables_consistent witness_env witness_cx witness_es
Proof
  simp[env_immutables_consistent_def, witness_env_def, artifact_env_def,
       empty_contract_type_artifact_def]
QED

Theorem witness_module_code:
  get_module_code witness_cx src = if src = NONE then SOME [] else NONE
Proof
  Cases_on `src` >> EVAL_TAC
QED

Theorem witness_functions_typed:
  functions_well_typed witness_cx
Proof
  simp[functions_well_typed_def, witness_module_code] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `lookup_callable_function _ _ [] = _` mp_tac >> EVAL_TAC
QED

Theorem witness_env_context_consistent:
  env_context_consistent witness_env witness_cx
Proof
  simp[env_context_consistent_def, witness_env_def, artifact_env_def,
       empty_contract_type_artifact_def, witness_tenv,
       fn_sigs_consistent_def, fn_sigs_live_def, fn_sigs_declared_complete_def,
       toplevel_vtypes_complete_def, bare_globals_complete_def,
       bare_global_assignable_complete_def, flag_members_complete_def,
       witness_module_code] >> EVAL_TAC >> simp[]
QED

Theorem witness_env_consistent:
  env_consistent witness_env witness_cx witness_es
Proof
  simp[env_consistent_def, witness_env_context_consistent,
       witness_scopes_consistent, witness_immutables_consistent]
QED

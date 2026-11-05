Theory bodyPtrBopInRuntimeState
Ancestors
  bodyPtrBopInLiveSourceFrame bodyPtrBopInSourceFrame compileEnv
  venomState vyperState vyperContext vyperInterpreter compileVyper

(* Reused finite runtime entry witness; transaction fields match the live
   source context, while allocations start at the reserved memory boundary. *)
Definition probe_runtime_s_def:
  probe_runtime_s = (init_venom_state "entry") with
    <| vs_alloca_next := 64;
       vs_block_ctx := empty_block_context with bc_number := 1w |>
End

Theorem live_call_context:
  call_ctx_rel probe_live_cx.txn probe_runtime_s.vs_call_ctx
    probe_runtime_s.vs_tx_ctx probe_runtime_s.vs_block_ctx
Proof
  simp[call_ctx_rel_def, probe_runtime_s_def, init_venom_state_def,
       empty_call_context_def, empty_tx_context_def, empty_block_context_def,
       probe_live_cx_def, probe_cx_def, empty_evaluation_context_def,
       empty_call_txn_def, tx_env_ok_def] >>
  rpt strip_tac >> Cases_on `n` >> simp[]
QED

Theorem probe_empty_compiler_maps:
  probe_cenv.ce_vars = FEMPTY /\ probe_cenv.ce_module_vars = FEMPTY
Proof
  EVAL_TAC
QED

Theorem live_runtime_state:
  !func. state_rel func probe_cenv probe_live_cx probe_es probe_runtime_s
Proof
  simp[state_rel_def, live_call_context, local_ptrs_rel_def, local_region_def,
       storage_vars_rel_def, transient_vars_rel_def, immutables_rel_def,
       probe_empty_compiler_maps] >>
  simp[probe_runtime_s_def, init_venom_state_def, empty_call_context_def,
       probe_live_cx_def, probe_cx_def, empty_evaluation_context_def,
       empty_call_txn_def, probe_es_def, initial_state_def,
       storage_rel_def, transient_rel_def, accounts_rel_def, logs_rel_def,
       initial_machine_state_def, contract_storage_def, contract_transient_def,
       accounts_agree_def, transient_agree_def, storage_agree_def,
       get_module_code_def, lookup_var_slot_from_layout_def]
QED

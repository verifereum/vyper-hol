(* The call premises read only the transaction's environment (target,
   sender, value, calldata, block), not which function it calls or with
   which arguments: the call theorem may take tx's function and arguments
   from the calldata. *)
Theory callPremiseDispatch
Ancestors
  e2eDefs vyperContext vyperState vyperInterpreter vyperLookupStorage
  vyperStorageLayoutSafety vyperTypeInitialState vyperTypeContractSoundness

(* Contexts that differ only in the transaction (same target) and stack. *)
Definition same_call_env_def:
  same_call_env cx cx' <=>
    cx'.sources = cx.sources /\ cx'.layouts = cx.layouts /\
    cx'.txn.target = cx.txn.target /\
    cx'.nonreentrant_slot = cx.nonreentrant_slot
End

Theorem same_call_env_reads[local]:
  same_call_env cx cx' ==>
  get_module_code cx' = get_module_code cx /\
  get_tenv cx' = get_tenv cx /\
  lookup_var_slot_from_layout cx' = lookup_var_slot_from_layout cx /\
  (!b. get_storage_backend cx' b = get_storage_backend cx b)
Proof
  rw[same_call_env_def, FUN_EQ_THM, get_module_code_def, get_tenv_def,
     lookup_var_slot_from_layout_def] >>
  Cases_on `b` >> simp[get_storage_backend_def]
QED

Theorem same_call_env_storage[local]:
  same_call_env cx cx' ==>
  storage_var_info cx' = storage_var_info cx /\
  declared_storage_region cx' = declared_storage_region cx
Proof
  strip_tac >> drule same_call_env_reads >>
  rw[FUN_EQ_THM, storage_var_info_def, declared_storage_region_def]
QED

Theorem same_call_env_preds[local]:
  same_call_env cx cx' ==>
  (contract_storage_well_formed cx' st <=> contract_storage_well_formed cx st) /\
  (storage_layout_safe cx' <=> storage_layout_safe cx) /\
  (immutables_ready g vt cx' imms <=> immutables_ready g vt cx imms)
Proof
  strip_tac >> drule same_call_env_reads >> drule same_call_env_storage >>
  rpt strip_tac >> fs[same_call_env_def] >>
  simp[contract_storage_well_formed_def, well_formed_storage_def,
       storage_var_in_range_def, storage_layout_safe_def,
       well_formed_layout_def, nonreentrant_slot_separated_def,
       immutables_ready_def]
QED

Theorem initial_context_same_call_env[local]:
  !s l tx f vals.
  same_call_env (initial_evaluation_context s l tx NONE)
    (initial_evaluation_context s l
       (tx with <| function_name := f; args := vals |>) NONE)
Proof
  simp[same_call_env_def, initial_evaluation_context_def]
QED

Theorem call_premises_dispatch_invariant:
  !tops runtime_bc am tx es os f vals.
    (source_typing_ok tops am (tx with <| function_name := f; args := vals |>)
       <=> source_typing_ok tops am tx) /\
    (source_storage_ok tops am (tx with <| function_name := f; args := vals |>)
       <=> source_storage_ok tops am tx) /\
    (call_state_rel tops runtime_bc am
       (tx with <| function_name := f; args := vals |>) es
       <=> call_state_rel tops runtime_bc am tx es) /\
    (call_outcomes_ok am (tx with <| function_name := f; args := vals |>) os
       <=> call_outcomes_ok am tx os) /\
    (call_outcomes_storage_ok am (tx with <| function_name := f; args := vals |>) os
       <=> call_outcomes_storage_ok am tx os)
Proof
  rpt gen_tac >>
  qspecl_then [`am.sources`, `am.layouts`, `tx`, `f`, `vals`] assume_tac
    initial_context_same_call_env >>
  drule same_call_env_preds >> strip_tac >>
  simp[source_typing_ok_def, checked_contract_runtime_ready_def,
       call_tx_well_typed_def, source_storage_ok_def, call_outcomes_ok_def,
       call_outcomes_storage_ok_def,
       call_state_rel_def, tx_block_fields_rel_def, value_transfer_ok_def,
       accounts_after_transfer_def, source_deployment_rel_def,
       layouts_agree_def, loweringStateRelDefsTheory.tx_env_ok_def] >>
  fs[same_call_env_def, initial_evaluation_context_def]
QED

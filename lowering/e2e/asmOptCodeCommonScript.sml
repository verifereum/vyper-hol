(* Shared semantic boundary for the optimizer's shadow transaction.
   Updating code preserves storage observations, not source execution. *)
Theory asmOptCodeCommon
Ancestors
  e2eDefs accountsRelProps lowerDloadDefs vyperStorageLayoutSafety
  vyperLookupStorage vyperTypeContractSoundness vyperInterpreter

Theorem call_tx_well_typed_code_update:
  call_tx_well_typed tx /\ LENGTH c < 2 ** 256 ==>
  call_tx_well_typed (tx with code := c)
Proof
  simp[call_tx_well_typed_def]
QED

Theorem code_layout_valid_code_length:
  code_layout_valid vs ==> LENGTH vs.vs_code < 2 ** 256
Proof
  simp[code_layout_valid_def, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >> decide_tac
QED

Theorem initial_evaluation_context_code_update:
  initial_evaluation_context srcs layouts (tx with code := c) mid =
  (initial_evaluation_context srcs layouts tx mid with
     txn := ((initial_evaluation_context srcs layouts tx mid).txn with code := c))
Proof
  simp[initial_evaluation_context_def]
QED

Theorem storage_dead_txn_code_update:
  storage_dead (cx with txn := (cx.txn with code := c)) = storage_dead cx
Proof
  irule storage_dead_cx_cong >> simp[]
QED

Theorem agree_txn_code_update:
  accounts_agree (cx with txn := (cx.txn with code := c)) = accounts_agree cx /\
  transient_agree (cx with txn := (cx.txn with code := c)) = transient_agree cx /\
  request_agree (cx with txn := (cx.txn with code := c)) = request_agree cx
Proof
  irule agree_cx_cong >> simp[]
QED

Theorem declared_storage_region_txn_code_update:
  declared_storage_region (cx with txn := (cx.txn with code := c)) mid n subs =
  declared_storage_region cx mid n subs
Proof
  simp[declared_storage_region_def, vyperContextTheory.get_module_code_def,
       vyperContextTheory.get_tenv_def, vyperStateTheory.lookup_var_slot_from_layout_def]
QED

Theorem storage_var_info_txn_code_update:
  storage_var_info (cx with txn := (cx.txn with code := c)) mid n =
  storage_var_info cx mid n
Proof
  simp[storage_var_info_def, vyperContextTheory.get_module_code_def,
       vyperContextTheory.get_tenv_def, vyperStateTheory.lookup_var_slot_from_layout_def]
QED

Theorem get_storage_backend_txn_code_update:
  get_storage_backend (cx with txn := (cx.txn with code := c)) b =
  get_storage_backend cx b
Proof
  Cases_on `b` >> simp[vyperStateTheory.get_storage_backend_def]
QED

Theorem contract_storage_well_formed_txn_code_update:
  contract_storage_well_formed (cx with txn := (cx.txn with code := c)) st =
  contract_storage_well_formed cx st
Proof
  simp[contract_storage_well_formed_def, well_formed_storage_def,
       storage_var_in_range_def, storage_var_info_txn_code_update,
       get_storage_backend_txn_code_update,
       declared_storage_region_txn_code_update]
QED

Theorem storage_layout_safe_txn_code_update:
  storage_layout_safe (cx with txn := (cx.txn with code := c)) =
  storage_layout_safe cx
Proof
  simp[storage_layout_safe_def, well_formed_layout_def,
       nonreentrant_slot_separated_def, storage_var_info_txn_code_update,
       declared_storage_region_txn_code_update]
QED

Theorem call_outcomes_ok_code_update:
  call_outcomes_ok am (tx with code := c) os = call_outcomes_ok am tx os
Proof
  simp[call_outcomes_ok_def, initial_evaluation_context_code_update,
       contract_storage_well_formed_txn_code_update]
QED

Theorem call_outcomes_storage_ok_code_update:
  call_outcomes_storage_ok am (tx with code := c) os =
  call_outcomes_storage_ok am tx os
Proof
  simp[call_outcomes_storage_ok_def, initial_evaluation_context_code_update,
       contract_storage_well_formed_txn_code_update]
QED

Theorem source_storage_ok_code_update:
  source_storage_ok tops am (tx with code := c) = source_storage_ok tops am tx
Proof
  simp[source_storage_ok_def, initial_evaluation_context_code_update,
       contract_storage_well_formed_txn_code_update,
       storage_layout_safe_txn_code_update]
QED

Theorem source_deployment_rel_code_update:
  source_deployment_rel tops am (tx with code := c) =
  source_deployment_rel tops am tx
Proof
  simp[source_deployment_rel_def, layouts_agree_def]
QED

Theorem valid_vyper_call_code_update:
  valid_vyper_call tops (tx with code := c) calldata ret =
  valid_vyper_call tops tx calldata ret
Proof
  simp[valid_vyper_call_def]
QED

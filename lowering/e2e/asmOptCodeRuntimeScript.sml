(* Runtime boundary for the optimizer's unoptimized-code transaction. *)
Theory asmOptCodeRuntime
Ancestors
  asmOptCodeCommon e2eAsmOpt e2eSelfCodeFree vyperTypeInitialState
  vyperTypeContractSoundness loweringStateRelDefs e2eDefs vyperInterpreter
  vyperLoweringCorrect

Theorem source_typing_ok_code_update:
  source_typing_ok tops am tx /\ LENGTH c < 2 ** 256 ==>
  source_typing_ok tops am (tx with code := c)
Proof
  pure_rewrite_tac [source_typing_ok_def] >> strip_tac >>
  qexists_tac `art` >>
  gvs[checked_contract_runtime_ready_def, immutables_ready_def,
      initial_evaluation_context_def, vyperContextTheory.get_tenv_def,
      vyperContextTheory.get_module_code_def, call_tx_well_typed_def] >>
  metis_tac[]
QED

Theorem external_call_dead_code_update:
  external_call_dead (tx with code := c) res = external_call_dead tx res
Proof
  PairCases_on `res` >>
  simp[external_call_dead_def, initial_evaluation_context_code_update,
       storage_dead_txn_code_update]
QED

Theorem tx_return_bytes_code_update:
  tx_return_bytes tops ret (tx with code := c) v bytes =
  tx_return_bytes tops ret tx v bytes
Proof
  simp[tx_return_bytes_def]
QED

Theorem external_call_result_rel_code_update:
  external_call_result_rel tops ret (tx with code := c) res vr =
  external_call_result_rel tops ret tx res vr
Proof
  PairCases_on `res` >>
  simp[external_call_result_rel_def, initial_evaluation_context_code_update,
       agree_txn_code_update, tx_return_bytes_code_update]
QED

Theorem source_unit_execution_correct_code_update:
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  ~program_reads_self_code tops ==>
  (source_unit_execution_correct tops ret am (tx with code := c) unit vs =
   source_unit_execution_correct tops ret am tx unit vs)
Proof
  strip_tac >>
  simp[source_unit_execution_correct_def, source_unit_execution_correct_at_def,
       call_external_self_code_free, external_call_result_rel_code_update]
QED

Theorem call_result_rel_at_code_update:
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  ~program_reads_self_code tops ==>
  (call_result_rel_at gobs tops ret am (tx with code := c) es r es' =
   call_result_rel_at gobs tops ret am tx es r es')
Proof
  strip_tac >>
  simp[call_result_rel_at_def, call_external_self_code_free,
       initial_evaluation_context_code_update, agree_txn_code_update,
       tx_return_bytes_code_update]
QED

Theorem call_result_rel_code_update:
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  ~program_reads_self_code tops ==>
  (call_result_rel tops ret am (tx with code := c) es r es' =
   call_result_rel tops ret am tx es r es')
Proof
  strip_tac >> simp[call_result_rel_def, call_result_rel_at_code_update]
QED

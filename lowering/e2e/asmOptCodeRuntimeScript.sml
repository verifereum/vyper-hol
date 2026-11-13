(* Runtime boundary for the optimizer's unoptimized-code transaction. *)
Theory asmOptCodeRuntime
Ancestors
  asmOptCodeCommon e2eAsmOpt e2eSelfCodeFree vyperTypeInitialState
  vyperTypeContractSoundness loweringStateRelDefs e2eDefs vyperInterpreter
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect e2eEntry o1PassContract

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

Theorem gas_variant_outcomes:
  gas_variant si so ==> si.vs_outcomes = so.vs_outcomes
Proof
  rw[gas_variant_def] >> pop_assum SUBST1_TAC >> simp[]
QED

Theorem gas_variant_call_ctx:
  gas_variant si so ==> si.vs_call_ctx = so.vs_call_ctx
Proof
  rw[gas_variant_def] >> pop_assum SUBST1_TAC >> simp[]
QED

Theorem gas_variant_initial_venom_state_rel:
  gas_variant si so /\ initial_venom_state_rel tops am tx so ==>
  initial_venom_state_rel tops am tx si
Proof
  rw[gas_variant_def] >>
  qpat_x_assum `so = _` SUBST_ALL_TAC >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def]
QED

(* Source lowering is stable under the pipeline's gas-reading replay.  Keep
   the entry facts together so later memory stages use the same source run. *)
Theorem runtime_source_gas_variant:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_storage_ok tops am tx /\ source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  call_outcomes_ok am tx vs.vs_outcomes /\ gas_variant vs_in vs /\
  code_layout_valid vs ==>
  initial_venom_state_rel tops am tx vs_in /\
  valid_vyper_call tops tx vs_in.vs_call_ctx.cc_calldata ret /\
  call_outcomes_ok am tx vs_in.vs_outcomes /\ code_layout_valid vs_in /\
  source_unit_execution_correct tops ret am tx unit vs_in
Proof
  strip_tac >>
  `initial_venom_state_rel tops am tx vs_in` by
    (irule gas_variant_initial_venom_state_rel >> metis_tac[]) >>
  `vs_in.vs_outcomes = vs.vs_outcomes /\
   vs_in.vs_call_ctx = vs.vs_call_ctx` by
    metis_tac[gas_variant_outcomes, gas_variant_call_ctx] >>
  `code_layout_valid vs_in` by metis_tac[gas_variant_code_layout_valid] >>
  simp[] >> irule lower_vyper_runtime_unit_correct >>
  simp[] >> qexists_tac `rpolicy` >> simp[]
QED

(* The source-to-memory boundary supplies the raw pipeline's three dload
   invariants from one source execution contract, without exposing internals. *)
Theorem runtime_source_dload_invariants:
  !tops rpolicy unit am tx ret vs.
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_storage_ok tops am tx /\ source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  call_outcomes_ok am tx vs.vs_outcomes /\ code_layout_valid vs /\
  (!marks. ~source_exempt tops
    (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings) am tx)) ==>
  mem_inv dload_offset_ok unit.cu_context vs /\
  mem_inv dload_headroom_ok unit.cu_context vs /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                            s.vs_code = vs.vs_code /\
                            s.vs_data_section = vs.vs_data_section)
    unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lower_vyper_runtime_unit_dload_offset_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_dload_headroom_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_dload_in_section >> simp[]
QED

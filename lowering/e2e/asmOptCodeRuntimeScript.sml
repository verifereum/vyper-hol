Theory asmOptCodeRuntime
Ancestors
  e2eDefs e2eSelfCodeFree e2eComposition asmOptCodeCommon e2eAsmOpt
  selfCodeFreeContext
  vyperLoweringCorrect codegenEntrySim
  accountsRelProps vyperInterpreter codegenAsmOpt contextCodegenRel
  asmFrameRel o1PassContract codegenRel callTrace passSimulationDefs
  vyperStorageLayoutSafety vyperTypeInitialState vyperTypeContractSoundness

val _ = Parse.hide "tops";

Theorem runtime_asm_compose:
  vs_in.vs_outcomes = MAP SND (call_trace es) /\
  H = storage_trace_horizon
        (source_storage_trace am tx vs_in.vs_outcomes gobs) /\
  (?fuel. external_call_result_rel H tops ret tx
    (call_external (SOME vs_in.vs_outcomes) gobs am tx)
    (run_context fuel unit.cu_context vs_in)) /\
  ctx_sim (external_call_dead H tx
    (call_external (SOME vs_in.vs_outcomes) gobs am tx))
    unit.cu_context out.po_unit.cu_context vs_in vs /\
  generate_context_plan out.po_unit.cu_context = SOME cplan /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  asm_opt_finalizer rpolicy prog = SOME prog' /\ unit_shape_ok out.po_unit /\
  codegen_context_obligations (raw_reachable vs) out.po_unit.cu_context cplan /\
  codegen_reachability_package (raw_reachable vs) out.po_unit.cu_context vs /\
  label_flow_ok out.po_unit.cu_context /\
  code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context /\
  sym_unit_static_ok out.po_unit /\
  vs.vs_code = assemble prog ++ vs.vs_data_section /\
  codegen_asm_entry_rel cplan prog vs (entry_asm_state vs es) /\
  asm_frame_rel prog' vs.vs_data_section es
    (entry_asm_state vs es with as_code := assemble prog' ++ vs.vs_data_section) es ==>
  ?r es'. run_call es = SOME (r, es') /\
    (frame_resource_starved es r es' \/
     call_result_rel_at gobs tops ret am tx es r es')
Proof
  rpt strip_tac >>
  drule external_call_result_rel_terminates >> strip_tac >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  rewrite_tac[ctx_sim_def] >> disch_then drule >>
  disch_then (qx_choose_then `outfuel` assume_tac) >>
  drule_all external_call_result_rel_dead_transport >> strip_tac >>
  drule_all codegen_correct_asm_opt >>
  disch_then (qspec_then `outfuel` strip_assume_tac)
  >- metis_tac[] >>
  gvs[] >>
  drule_all external_call_result_rel_frame >>
  metis_tac[]
QED

Theorem external_call_dead_code_update:
  external_call_dead H (tx with code := c) res =
  external_call_dead H tx res
Proof
  PairCases_on `res` >> simp[external_call_dead_def]
QED

Theorem external_call_result_rel_code_update:
  external_call_result_rel H tops ret (tx with code := c) res vr =
  external_call_result_rel H tops ret tx res vr
Proof
  PairCases_on `res` >>
  simp[external_call_result_rel_def, initial_evaluation_context_code_update,
       agree_txn_code_update, tx_return_bytes_def]
QED

Theorem call_result_rel_at_code_update:
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  ~program_reads_self_code tops ==>
  (call_result_rel_at gobs tops ret am (tx with code := c) es r es' =
   call_result_rel_at gobs tops ret am tx es r es')
Proof
  rpt strip_tac >>
  drule_all source_storage_trace_self_code_free >>
  disch_then (qspec_then `c` assume_tac) >>
  drule_all call_external_self_code_free >>
  disch_then (qspecl_then [`SOME (MAP SND (call_trace es))`, `gobs`, `c`] assume_tac) >>
  simp[call_result_rel_at_def, call_success_rel_def,
       initial_evaluation_context_code_update, agree_txn_code_update,
       tx_return_bytes_def]
QED

Theorem source_typing_ok_code_update:
  source_typing_ok tops am tx /\ LENGTH c < 2 ** 256 ==>
  source_typing_ok tops am (tx with code := c)
Proof
  pure_rewrite_tac [source_typing_ok_def] >> strip_tac >>
  qexists_tac `art` >>
  `call_tx_well_typed (tx with code := c)` by
    (irule call_tx_well_typed_code_update >> simp[]) >>
  gvs[checked_contract_runtime_ready_def, immutables_ready_def,
      initial_evaluation_context_code_update, vyperContextTheory.get_tenv_def,
      vyperContextTheory.get_module_code_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem storage_well_formed_on_txn_code_update:
  storage_well_formed_on (cx with txn := (cx.txn with code := c)) st regions =
  storage_well_formed_on cx st regions
Proof
  irule vyperCallFiniteStorageSupportTheory.storage_well_formed_on_target >>
  simp[]
QED

Theorem storage_trace_backends_well_formed_txn_code_update:
  storage_trace_backends_well_formed
    (cx with txn := (cx.txn with code := c)) regions obs =
  storage_trace_backends_well_formed cx regions obs
Proof
  Induct_on `obs`
  >- simp[vyperStorageFootprintTheory.storage_trace_backends_well_formed_def] >>
  qx_gen_tac `ob` >> Cases_on `ob` >>
  simp[vyperStorageFootprintTheory.storage_trace_backends_well_formed_def,
       storage_well_formed_on_txn_code_update]
QED

Theorem source_storage_ok_code_update:
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  ~program_reads_self_code tops ==>
  (source_storage_ok am (tx with code := c) os gobs =
   source_storage_ok am tx os gobs)
Proof
  rpt strip_tac >>
  simp[source_storage_ok_def, source_storage_trace_self_code_free,
       initial_evaluation_context_code_update] >>
  pairarg_tac >> simp[storage_well_formed_on_txn_code_update]
QED

Theorem call_outcomes_storage_ok_code_update:
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
  ~program_reads_self_code tops ==>
  (call_outcomes_storage_ok am (tx with code := c) os gobs =
   call_outcomes_storage_ok am tx os gobs)
Proof
  rpt strip_tac >>
  simp[call_outcomes_storage_ok_def, source_storage_trace_self_code_free,
       initial_evaluation_context_code_update,
       storage_trace_backends_well_formed_txn_code_update]
QED

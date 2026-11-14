(* Runtime boundary for the optimizer's unoptimized-code transaction. *)
Theory asmOptCodeRuntime
Ancestors
  asmOptCodeCommon e2eAsmOpt e2eSelfCodeFree vyperTypeInitialState
  vyperTypeContractSoundness loweringStateRelDefs e2eDefs vyperInterpreter
  vyperLoweringCorrect loweringRuntimeCorrect loweringMemCorrect e2eEntry o1PassContract
  e2eComposition e2eProducers o1PipelineCorrect loweringShapeProps loweringShapeSource
  runtimeSymSrcUnit codegenAsmOpt contextCodegenRel ptrDiscipline immutableCodeLayout
  lowerDloadDefs o1CodeEndOffset

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

(* Optimizer entry facts, with the source transaction pinned to that entry. *)
Theorem runtime_asm_entry:
  call_state_rel tops (assemble prog') am tx es /\
  codegen_assembly rpolicy u = SOME prog /\ unit_shape_ok u /\
  assemble prog' <> [] /\ source_typing_ok tops am tx /\
  source_storage_ok tops am tx /\
  valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
  call_outcomes_ok am tx (MAP SND (call_trace es)) ==>
  !cplan. ?vs txp.
  vs = opt_entry_state prog prog' cplan es /\ txp = tx with code := vs.vs_code /\
  initial_venom_state_rel tops am txp vs /\
  codegen_asm_entry_rel cplan prog vs (entry_asm_state vs es) /\
  asm_frame_rel prog' vs.vs_data_section es
    (entry_asm_state vs es with as_code := assemble prog' ++ vs.vs_data_section) es /\
  code_layout_valid vs /\ vs.vs_outcomes = MAP SND (call_trace es) /\
  vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
  vs.vs_fmp = vs.vs_initial_fmp /\ ~vs.vs_call_ctx.cc_static /\
  o1_initial_state_ok vs /\ vs.vs_code = assemble prog ++ vs.vs_data_section /\
  source_typing_ok tops am txp /\ source_storage_ok tops am txp /\
  valid_vyper_call tops txp vs.vs_call_ctx.cc_calldata ret /\
  call_outcomes_ok am txp vs.vs_outcomes /\ source_deployment_rel tops am txp /\
  ALOOKUP am.sources tx.target = SOME [(NONE, tops)]
Proof
  rpt strip_tac >>
  qabbrev_tac `vs = opt_entry_state prog prog' cplan es` >>
  qabbrev_tac `txp = tx with code := vs.vs_code` >>
  qexistsl_tac [`vs`, `txp`] >>
  conj_tac >- simp[Abbr `vs`] >> conj_tac >- simp[Abbr `txp`] >>
  drule opt_entry_initial_venom_state_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  drule_all opt_entry_codegen_asm_entry_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  drule_all opt_entry_asm_frame_rel >>
  disch_then (qspecl_then [`prog`, `cplan`] assume_tac) >>
  drule_all opt_entry_code_layout_valid >>
  disch_then (qspec_then `cplan` assume_tac) >>
  drule opt_entry_fields >>
  disch_then (qspecl_then [`prog`, `cplan`, `vs`] mp_tac) >>
  simp[] >> strip_tac >>
  `source_typing_ok tops am txp` by
    (simp[Abbr `txp`] >> irule source_typing_ok_code_update >>
     drule code_layout_valid_code_length >> simp[Abbr `vs`]) >>
  simp[Abbr `txp`, Abbr `vs`, source_storage_ok_code_update,
       valid_vyper_call_code_update, call_outcomes_ok_code_update,
       source_deployment_rel_code_update] >>
  gvs[call_state_rel_def, source_deployment_rel_def]
QED

(* Raw source execution supplies the memory interface consumed by O1. *)
Theorem runtime_source_memory:
  !tops rpolicy unit am tx ret vs.
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_storage_ok tops am tx /\ source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\
  call_outcomes_ok am tx vs.vs_outcomes /\ code_layout_valid vs /\
  o1_source_unit_ok unit /\
  (!marks. ~source_exempt tops (call_external (SOME vs.vs_outcomes)
    (gas_explicit marks vs.vs_gas_readings) am tx)) ==>
  raw_unit_memory_ok unit.cu_context vs /\
  ptr_discipline 0 unit.cu_context vs /\
  taint_within (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
    unit.cu_context vs /\
  mem_inv dload_offset_ok unit.cu_context vs /\
  mem_inv dload_headroom_ok unit.cu_context vs /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
    s.vs_code = vs.vs_code /\ s.vs_data_section = vs.vs_data_section)
    unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  `~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx)` by
    (first_x_assum (qspec_then `[]` mp_tac) >>
     simp[gasSummaryTheory.gas_explicit_def, gasOracleReplayTheory.gas_prefix_def]) >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  drule runtime_source_dload_invariants >>
  disch_then (qspecl_then [`am`, `tx`, `ret`, `vs`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  drule lower_vyper_runtime_unit_memory_ok >>
  disch_then (qspecl_then [`am`, `tx`, `ret`, `vs`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >> simp[] >>
  metis_tac[external_call_dead_observations]
QED

(* Prepare the raw O1 simulation and the static codegen boundary. *)
Theorem runtime_pipeline_prepare:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ ~program_reads_self_code tops /\
  o1_pipeline rpolicy unit = SOME out /\ o1_source_unit_ok unit /\
  unit_entry_no_params unit /\ unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  code_layout_valid vs /\ vs.vs_code = assemble prog ++ vs.vs_data_section /\
  assemble prog <> [] /\ vs.vs_fmp = vs.vs_initial_fmp /\
  ~vs.vs_call_ctx.cc_static /\ o1_initial_state_ok vs ==>
  label_flow_ok out.po_unit.cu_context /\ sym_unit_static_ok out.po_unit /\
  ?vs_in. gas_variant vs_in vs /\
    (raw_unit_memory_ok unit.cu_context vs_in /\
     ptr_discipline 0 unit.cu_context vs_in /\
     taint_within (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
       unit.cu_context vs_in /\
     mem_inv dload_offset_ok unit.cu_context vs_in /\
     mem_inv dload_headroom_ok unit.cu_context vs_in /\
     mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
       s.vs_code = vs_in.vs_code /\ s.vs_data_section = vs_in.vs_data_section)
       unit.cu_context vs_in ==>
     ctx_sim (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
       unit.cu_context out.po_unit.cu_context vs_in vs /\
     o1_lowered_inv out.po_unit.cu_context vs /\
     code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context)
Proof
  strip_tac >>
  `o1_run_state_ok vs` by fs[o1_run_state_ok_def] >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >> simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >>
     simp[staticLayoutDefsTheory.reserved_intervals_wf_def]) >>
  `dead_wf (external_call_dead tx
    (call_external (SOME vs.vs_outcomes) [] am tx))` by simp[external_call_dead_wf] >>
  `LENGTH vs.vs_data_section < dimword (:256) DIV 2` by
    (drule_all code_layout_valid_data_section_bound >> simp[]) >>
  drule_all lower_vyper_runtime_unit_sym_src_ok >> strip_tac >>
  `label_flow_ok out.po_unit.cu_context` by
    (irule o1_pipeline_label_flow_ok >> metis_tac[]) >>
  `sym_unit_static_ok out.po_unit` by
    (irule o1_pipeline_sym_unit_static_ok >> metis_tac[]) >>
  simp[] >> drule_all o1_pipeline_code_end_offset_ok >> simp[]
QED

(* Discharge O1's conditional simulation using the source-memory boundary. *)
Theorem runtime_pipeline_nonexempt:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ source_typing_ok tops am tx /\
  source_storage_ok tops am tx /\ source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\ call_outcomes_ok am tx vs.vs_outcomes /\
  code_layout_valid vs /\ gas_variant vs_in vs /\
  o1_source_unit_ok unit /\ o1_pipeline rpolicy unit = SOME out /\
  generate_context_plan out.po_unit.cu_context = SOME cplan /\ unit_shape_ok out.po_unit /\
  vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
  (!marks. ~source_exempt tops (call_external (SOME vs_in.vs_outcomes)
    (gas_explicit marks vs_in.vs_gas_readings) am tx)) /\
  (raw_unit_memory_ok unit.cu_context vs_in /\
   ptr_discipline 0 unit.cu_context vs_in /\
   taint_within (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
     unit.cu_context vs_in /\
   mem_inv dload_offset_ok unit.cu_context vs_in /\
   mem_inv dload_headroom_ok unit.cu_context vs_in /\
   mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
     s.vs_code = vs_in.vs_code /\ s.vs_data_section = vs_in.vs_data_section)
     unit.cu_context vs_in ==>
   ctx_sim (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
     unit.cu_context out.po_unit.cu_context vs_in vs /\
   o1_lowered_inv out.po_unit.cu_context vs /\
   code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context) ==>
  ctx_sim (external_call_dead tx (call_external (SOME vs_in.vs_outcomes) [] am tx))
    unit.cu_context out.po_unit.cu_context vs_in vs /\
  code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context /\
  codegen_context_obligations (raw_reachable vs) out.po_unit.cu_context cplan /\
  codegen_reachability_package (raw_reachable vs) out.po_unit.cu_context vs
Proof
  strip_tac >> drule_all runtime_source_gas_variant >> strip_tac >>
  `vs_in.vs_outcomes = vs.vs_outcomes` by metis_tac[gas_variant_outcomes] >>
  drule runtime_source_memory >>
  disch_then (qspecl_then [`am`, `tx`, `ret`, `vs_in`] mp_tac) >>
  impl_tac >- gvs[] >> strip_tac >>
  `ctx_sim (external_call_dead tx (call_external (SOME vs.vs_outcomes) [] am tx))
    unit.cu_context out.po_unit.cu_context vs_in vs /\
   o1_lowered_inv out.po_unit.cu_context vs /\
   code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context` by metis_tac[] >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> simp[]
QED

(* State-level composition belongs below both runtime consumers. *)
Theorem e2e_vyper_to_evm_states:
  !gobs tops ret am tx ctx ctx' vs_in vs_out es.
    vs_in.vs_outcomes = MAP SND (call_trace es) /\
    (?fuel. external_call_result_rel tops ret tx
              (call_external (SOME vs_in.vs_outcomes) gobs am tx)
              (run_context fuel ctx vs_in)) /\
    (~source_exempt tops (call_external (SOME vs_in.vs_outcomes) gobs am tx) ==>
       ctx_sim (external_call_dead tx
                  (call_external (SOME vs_in.vs_outcomes) gobs am tx))
         ctx ctx' vs_in vs_out /\
       !fuel. ?r es'.
         run_call es = SOME (r, es') /\
         (frame_resource_starved es r es' \/ precompile_call_starved es \/
          venom_frame_rel es r es' (run_context fuel ctx' vs_out)))
    ==>
    ?r es'. run_call es = SOME (r, es') /\
            (frame_resource_starved es r es' \/ precompile_call_starved es \/
             call_result_rel_at gobs tops ret am tx es r es')
Proof
  rpt strip_tac >>
  qspec_then `es` strip_assume_tac run_call_total >>
  qexistsl_tac [`r`, `es'`] >> simp[] >>
  Cases_on `source_exempt tops (call_external (SOME vs_in.vs_outcomes) gobs am tx)`
  >- (disj2_tac >> disj2_tac >>
      irule source_exempt_call_result_rel >> gvs[]) >>
  gvs[] >>
  drule_all external_call_result_rel_terminates >> strip_tac >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  `terminates (run_context fuel' ctx' vs_out)` by
    metis_tac[dead_result_rel_terminates] >>
  qpat_x_assum `!fuel. frame_resource_starved es r es' \/ _`
    (qspec_then `fuel'` strip_assume_tac) >>
  gvs[] >>
  drule_all external_call_result_rel_dead_transport >> strip_tac >>
  drule_all external_call_result_rel_frame >> simp[]
QED

Theorem runtime_asm_compose:
  vs_in.vs_outcomes = MAP SND (call_trace es) /\
  (?fuel. external_call_result_rel tops ret tx
    (call_external (SOME vs_in.vs_outcomes) gobs am tx)
    (run_context fuel unit.cu_context vs_in)) /\
  ctx_sim (external_call_dead tx (call_external (SOME vs_in.vs_outcomes) [] am tx))
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
    (frame_resource_starved es r es' \/ call_result_rel tops ret am tx es r es')
Proof
  strip_tac >>
  `?r es'. run_call es = SOME (r, es') /\
    (frame_resource_starved es r es' \/ call_result_rel_at gobs tops ret am tx es r es')`
    suffices_by metis_tac[call_result_rel_at_imp] >>
  irule (SRULE [] (Q.INST [`precompile_call_starved` |-> `K F`]
    e2e_vyper_to_evm_states)) >>
  qexistsl_tac [`unit.cu_context`, `out.po_unit.cu_context`, `vs_in`, `vs`] >>
  rpt conj_tac
  >~ [`external_call_result_rel`] >- (qexists_tac `fuel` >> first_assum ACCEPT_TAC)
  >~ [`call_trace`] >- first_assum ACCEPT_TAC >>
  strip_tac >> conj_tac
  >- metis_tac[external_call_dead_observations] >>
  qx_gen_tac `fuel'` >>
  qspecl_then [`fuel'`, `rpolicy`, `out.po_unit`, `cplan`, `prog`, `prog'`,
               `raw_reachable vs`, `vs`, `es`] mp_tac codegen_correct_asm_opt >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

(* Execute the prepared optimizer entry, including exempt source failures. *)
Theorem runtime_asm_execute:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ ~program_reads_self_code tops /\
  source_typing_ok tops am tx /\ source_storage_ok tops am tx /\
  source_deployment_rel tops am tx /\
  valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  initial_venom_state_rel tops am tx vs /\ call_outcomes_ok am tx vs.vs_outcomes /\
  o1_pipeline rpolicy unit = SOME out /\ o1_source_unit_ok unit /\
  unit_entry_no_params unit /\ unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  generate_context_plan out.po_unit.cu_context = SOME cplan /\ unit_shape_ok out.po_unit /\
  codegen_assembly rpolicy out.po_unit = SOME prog /\
  asm_opt_finalizer rpolicy prog = SOME prog' /\ assemble prog <> [] /\
  code_layout_valid vs /\ vs.vs_code = assemble prog ++ vs.vs_data_section /\
  vs.vs_initial_fmp = n2w cplan.cp_initial_fmp /\
  vs.vs_fmp = vs.vs_initial_fmp /\ ~vs.vs_call_ctx.cc_static /\ o1_initial_state_ok vs /\
  vs.vs_outcomes = MAP SND (call_trace es) /\
  codegen_asm_entry_rel cplan prog vs (entry_asm_state vs es) /\
  asm_frame_rel prog' vs.vs_data_section es
    (entry_asm_state vs es with as_code := assemble prog' ++ vs.vs_data_section) es ==>
  ?r es'. run_call es = SOME (r, es') /\
    (frame_resource_starved es r es' \/ call_result_rel tops ret am tx es r es')
Proof
  strip_tac >> drule_all runtime_pipeline_prepare >>
  disch_then (qspecl_then [`tx`, `am`] strip_assume_tac) >>
  drule_all runtime_source_gas_variant >> strip_tac >>
  `vs_in.vs_outcomes = vs.vs_outcomes` by metis_tac[gas_variant_outcomes] >>
  `?marks. source_unit_execution_correct_at
    (gas_explicit marks vs_in.vs_gas_readings) tops ret am tx unit vs_in` by
    metis_tac[source_unit_execution_correct_def] >>
  Cases_on `?marks'. source_exempt tops (call_external (SOME vs_in.vs_outcomes)
    (gas_explicit marks' vs_in.vs_gas_readings) am tx)`
  >- (pop_assum (qx_choose_then `m` assume_tac) >>
      qspec_then `es` strip_assume_tac run_call_total >>
      qexistsl_tac [`r`, `es'`] >> simp[] >> disj2_tac >>
      irule call_result_rel_at_imp >>
      qexists_tac `gas_explicit m vs_in.vs_gas_readings` >>
      irule source_exempt_call_result_rel >> metis_tac[]) >>
  qpat_x_assum `~?marks'. _`
    (assume_tac o PURE_REWRITE_RULE [NOT_EXISTS_THM]) >>
  `?fuel. external_call_result_rel tops ret tx
    (call_external (SOME vs_in.vs_outcomes)
      (gas_explicit marks vs_in.vs_gas_readings) am tx)
    (run_context fuel unit.cu_context vs_in)` by
    metis_tac[source_unit_execution_correct_at_def] >>
  `!marks. ~source_exempt tops (call_external (SOME vs_in.vs_outcomes)
    (gas_explicit marks vs_in.vs_gas_readings) am tx)` by metis_tac[] >>
  drule_all runtime_pipeline_nonexempt >> strip_tac >>
  irule runtime_asm_compose >>
  qexistsl_tac [`cplan`, `gas_explicit marks vs_in.vs_gas_readings`, `out`,
    `prog`, `prog'`, `rpolicy`, `unit`, `vs`, `vs_in`] >> simp[] >>
  qexists_tac `fuel` >> gvs[]
QED

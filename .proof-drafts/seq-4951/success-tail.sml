  `source_storage_ok tops am txp` by
    simp[Abbr `txp`, source_storage_ok_code_update] >>
  `dispatched_vyper_call tops txp vs.vs_call_ctx.cc_calldata ret` by
    gvs[dispatched_vyper_call_def, Abbr `txp`] >>
  `call_outcomes_ok am txp vs.vs_outcomes` by
    simp[Abbr `txp`, call_outcomes_ok_code_update] >>
  drule_all runtime_pipeline_prepare >>
  disch_then (qspecl_then [`txp`, `am`] strip_assume_tac) >>
  `initial_venom_state_rel tops am txp vs_in` by
    (irule gas_variant_initial_venom_state_rel >> metis_tac[]) >>
  `vs_in.vs_outcomes = vs.vs_outcomes /\
   vs_in.vs_call_ctx = vs.vs_call_ctx` by
    metis_tac[gas_variant_outcomes, gas_variant_call_ctx] >>
  `code_layout_valid vs_in` by
    metis_tac[gas_variant_code_layout_valid] >>
  `source_unit_execution_correct tops ret am txp unit vs_in` by
    (irule lower_vyper_runtime_unit_correct_dispatched >>
     simp[] >> qexists_tac `rpolicy` >> simp[]) >>
  `?marks. source_unit_execution_correct_at
    (gas_explicit marks vs_in.vs_gas_readings)
      tops ret am txp unit vs_in` by
    metis_tac[source_unit_execution_correct_def] >>
  `ALOOKUP am.sources tx.target = SOME [(NONE, tops)]` by
    fs[call_state_rel_def, source_deployment_rel_def] >>
  `?r es'. run_call es = SOME (r, es') /\
    (frame_resource_starved es r es' \/
     call_result_rel tops ret am txp es r es')`
    suffices_by simp[Abbr `txp`, call_result_rel_code_update] >>
  Cases_on `?m. source_exempt tops (call_external (SOME vs_in.vs_outcomes)
    (gas_explicit m vs_in.vs_gas_readings) am txp)`
  >- (pop_assum (qx_choose_then `m` assume_tac) >>
      qspec_then `es` strip_assume_tac run_call_total >>
      qexistsl_tac [`r`, `es'`] >> simp[] >> disj2_tac >>
      irule call_result_rel_at_imp >>
      qexists_tac `gas_explicit m vs_in.vs_gas_readings` >>
      irule source_exempt_call_result_rel >> metis_tac[]) >>
  qpat_x_assum `~?m. _`
    (assume_tac o PURE_REWRITE_RULE [NOT_EXISTS_THM]) >>
  `!marks. ~source_exempt tops (call_external (SOME vs_in.vs_outcomes)
    (gas_explicit marks vs_in.vs_gas_readings) am txp)` by metis_tac[] >>
  drule o1_source_unit_ok_no_dalloca >> strip_tac >>
  drule lower_vyper_runtime_unit_memory_ok_dispatched >>
  disch_then (qspecl_then [`am`, `txp`, `ret`, `vs_in`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `mem_inv dload_offset_ok unit.cu_context vs_in` by
    (irule lower_vyper_runtime_unit_dload_offset_ok_dispatched >>
     qexistsl_tac [`am`, `ret`, `rpolicy`, `tops`, `txp`] >> simp[]) >>
  `mem_inv dload_headroom_ok unit.cu_context vs_in` by
    (irule lower_vyper_runtime_unit_dload_headroom_ok >> metis_tac[]) >>
  `mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
     s.vs_code = vs_in.vs_code /\ s.vs_data_section = vs_in.vs_data_section)
     unit.cu_context vs_in` by
    (irule lower_vyper_runtime_unit_dload_in_section >> metis_tac[]) >>
  `ctx_sim (external_call_dead txp
     (call_external (SOME vs_in.vs_outcomes) [] am txp))
     unit.cu_context out.po_unit.cu_context vs_in vs /\
   o1_lowered_inv out.po_unit.cu_context vs /\
   code_end_offset_ok (raw_reachable vs) out.po_unit.cu_context` by
    metis_tac[] >>
  drule_all o1_pipeline_memory_obligations_raw >> strip_tac >>
  drule_all o1_pipeline_codegen_obligations >> strip_tac >>
  irule runtime_asm_compose >>
  qexistsl_tac [`cplan`, `gas_explicit marks vs_in.vs_gas_readings`, `out`,
    `prog`, `prog'`, `rpolicy`, `unit`, `vs`, `vs_in`] >> simp[] >>
  metis_tac[source_unit_execution_correct_at_def]
QED

Theorem vyper_call_correct_asm_opt:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper asm_opt_finalizer policy tops = SOME (deploy_bc, runtime_bc) /\
    ~program_reads_self_code tops /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    dispatched_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    call_outcomes_storage_ok am tx (MAP SND (call_trace es))
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       call_result_rel tops ret am tx es r es')
Proof
  rpt strip_tac >>
  drule_all call_state_rel_call_outcomes_ok >> strip_tac >>
  qpat_x_assum `call_outcomes_storage_ok _ _ _` kall_tac >>
  drule compile_vyper_runtime_phases_asm_opt >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `assemble prog <> []` by
    metis_tac[codegenAsmProgOkTheory.codegen_assembly_nonempty] >>
  drule compile_vyper_runtime_nonempty_asm_opt >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`] mp_tac
    opt_entry_initial_venom_state_rel >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `out.po_unit`]
    mp_tac opt_entry_codegen_asm_entry_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `out.po_unit`]
    mp_tac opt_entry_asm_frame_rel >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`, `rpolicy`,
               `out.po_unit`] mp_tac opt_entry_code_layout_valid >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`tops`, `prog`, `prog'`, `am`, `tx`, `es`, `cplan`,
               `opt_entry_state prog prog' cplan es`] mp_tac opt_entry_fields >>
  impl_tac >- simp[] >> strip_tac >>
  qabbrev_tac `vs = opt_entry_state prog prog' cplan es` >>
  (* The Venom run sees the unoptimized code: run the source side on txp. *)
  qabbrev_tac `txp = tx with code := vs.vs_code` >>
  `source_typing_ok tops am txp` by
    (simp[Abbr `txp`] >> irule source_typing_ok_code_update >>
     drule code_layout_valid_code_length >> simp[]) >>
  `source_deployment_rel tops am txp` by
    (simp[Abbr `txp`, source_deployment_rel_code_update] >>
     fs[call_state_rel_def]) >>
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

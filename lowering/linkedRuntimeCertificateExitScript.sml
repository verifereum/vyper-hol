(* Take the nonexempt linked certificate's exit at a fixed GAS filling. *)
Theory linkedRuntimeCertificateExit
Ancestors
  sourceUnitExecutionMods e2eCorrectness[qualified] e2eModsDefs
  vyperInterpreter vyperStorageFootprint vyperContext vyperLoweringCorrect
  ptrDiscipline passSimulationDefs fragExec fragExecMem venomInst venomExecSemantics
  finite_map list

Theorem linked_runtime_certificate_exit:
  o1_source_unit_ok unit /\
  source_unit_execution_correct_with_mods shadow_ctx marks mods exps ret am tx unit vs /\
  call_storage_ok am tx vs.vs_outcomes
    (gas_explicit marks vs.vs_gas_readings ++ tail) /\
  ~source_exempt_mods mods
    (call_external (SOME vs.vs_outcomes)
      (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) ==>
  ?fn fuel.
    unit.cu_context.ctx_entry = SOME "__entry" /\
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME "__entry" /\
    terminates (run_context fuel unit.cu_context vs) /\
    (!n. mem_safe_blocks n unit.cu_context fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)) /\
    (!H. valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
          (initial_state am []) H
          (source_storage_trace am tx vs.vs_outcomes
             (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
         external_call_result_rel_mods H mods exps ret tx
           (call_external (SOME vs.vs_outcomes)
             (gas_explicit marks vs.vs_gas_readings ++ tail) am tx)
           (run_context fuel unit.cu_context vs) /\
         !n. ptr_safe_blocks
           (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
           0 n unit.cu_context fn [] FEMPTY entry_taint
           (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|>)) /\
    storage_trace_domain (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [])
      (source_storage_trace am tx vs.vs_outcomes
         (gas_explicit marks vs.vs_gas_readings ++ tail))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `source_unit_execution_correct_with_mods _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [source_unit_execution_correct_with_mods_def])
  >- (qpat_x_assum `!tail. ~call_storage_ok _ _ _ _`
        (qspec_then `tail` mp_tac) >> asm_rewrite_tac[])
  >- (qpat_assum `!tail. call_external_trace _ _ _ _ = _`
        (qspec_then `tail` (strip_assume_tac o MATCH_MP call_external_trace_result)) >>
      fs[]) >>
  qpat_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `tail` (strip_assume_tac o MATCH_MP call_external_trace_result)) >>
  drule_all e2eCorrectnessTheory.selected_run >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `fuel` assume_tac) assume_tac) >>
  qexistsl_tac [`func`,`fuel`] >> asm_rewrite_tac[] >>
  Cases_on `r` >> fs[exit_result_def, terminates_def]
QED

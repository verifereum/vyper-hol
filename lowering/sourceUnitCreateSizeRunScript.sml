(* Preserve the selected certificate's CREATE-size clause at the actual
   terminating context run, not merely at a block-local execution. *)
Theory sourceUnitCreateSizeRun
Ancestors
  sourceUnitExecution vyperInterpreter fragGasOrigin fragGasMode fragGasPathMem
  fragExec

Theorem source_unit_create_size_run:
  !marks tops ret am tx unit vs.
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    call_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    ~source_exempt tops
      (call_external (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings) am tx) /\
    (!fn bb. lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
             lookup_block "__entry" fn.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
    ?fuel. exit_result (run_context fuel unit.cu_context vs) /\
      create_size_exit_ok unit.cu_context
        (FST (call_external (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings) am tx))
        (run_context fuel unit.cu_context vs)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_unit_execution_correct_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_unit_execution_correct_at_def,
                                      source_unit_execution_correct_with_def])
  >- (qpat_x_assum `!tail. ~_` (qspec_then `[]` mp_tac) >> simp[])
  >- (qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      drule call_external_trace_result >> strip_tac >> gvs[]) >>
  qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  drule call_external_trace_result >> strip_tac >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def] >> strip_tac >>
  drule gas_path_mem_exec >> strip_tac
  >- metis_tac[exit_result_def] >>
  qmatch_asmsub_abbrev_tac `run_from fuel unit.cu_context func s` >>
  `?bb. lookup_block "__entry" func.fn_blocks = SOME bb` by
    (Cases_on `lookup_block "__entry" func.fn_blocks` >> simp[] >>
     qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
     simp[Abbr `s`, run_from_def] >> metis_tac[exit_result_not_error]) >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[Abbr `s`] >>
  `s with vs_inst_idx := 0 = s` by simp[Abbr `s`] >>
  qexists_tac `SUC fuel` >>
  `run_context (SUC fuel) unit.cu_context vs =
      run_blocks (SUC fuel) unit.cu_context func s` by
    (qunabbrev_tac `s` >> irule run_context_run_blocks >> simp[]) >>
  drule_all run_blocks_run_from_no_phi >> simp[]
QED

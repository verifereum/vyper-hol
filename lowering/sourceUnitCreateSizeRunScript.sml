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
  drule_all sourceUnitExitSafeTheory.source_unit_execution_exit >>
  disch_then (qx_choosel_then [`func`, `shadow_ctx`, `r`] strip_assume_tac) >>
  qabbrev_tac `s = vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                                 vs_inst_idx := 0 |>` >>
  drule_all gas_origin_path_events >>
  disch_then (qx_choosel_then [`fuel`, `bb`]
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac kall_tac))) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `!fn bb. _ ==> phi_prefix_length _ = 0`
       (qspecl_then [`func`, `bb`] mp_tac) >> fs[Abbr `s`]) >>
  `s with vs_inst_idx := 0 = s` by simp[Abbr `s`] >>
  qexists_tac `SUC fuel` >>
  `run_context (SUC fuel) unit.cu_context vs =
      run_blocks (SUC fuel) unit.cu_context func s` by
    (qunabbrev_tac `s` >> irule run_context_run_blocks >> simp[]) >>
  qspecl_then [`fuel`, `unit.cu_context`, `func`, `s`, `bb`] mp_tac
    run_blocks_run_from_no_phi >> simp[]
QED

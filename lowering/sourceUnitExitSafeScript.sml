(*
 * The exit arm of one selected raw-unit execution gives the runs from the
 * unit's entry that S3's bridges take (loweringMemCorrect's
 * lower_vyper_runtime_unit_memory_ok and _dload_offset_ok,
 * loweringPtrCorrect's lower_vyper_runtime_unit_ptr_taint).
 *
 * At the certificate's own fixed marks, the storage guards rule out its
 * bad-storage arm and ~source_exempt its exempt arm.  On the exit arm,
 * gas_origin_path T ends in an exit, so the run from the entry is
 * memory-safe at every fuel; storage_trace_domain makes the observed
 * horizon valid, at which the arm gives the pointer-safe run.
 *
 * TOP-LEVEL:
 *   source_unit_exit_safe_runs -- the entry's memory-safe run and its
 *     pointer-safe run at the dead set of the observed horizon
 *   lower_vyper_runtime_unit_exit_mem_safe_blocks -- any memory path from
 *     the entry to an exit (the exit arm's, or a revert's) gives the
 *     memory-safe run
 *   source_unit_exit_ptr_safe_horizons -- the pointer-safe run at the dead
 *     set of every valid horizon of the certificate's source trace
 *)
Theory sourceUnitExitSafe
Ancestors
  sourceUnitExecution vyperStorageFootprint vyperInterpreter
  fragGasOrigin fragGasMode fragGasPathMem fragExecMem fragExec
  memSafeRun entryDispatchMem acceptedContextPhi compileVyper

(* From an exit along a memory path, the run from its start is memory-safe
   at every fuel. *)
Theorem gas_path_mem_exit_mem_safe_run[local]:
  !ctx func s n r.
    gas_path_mem ctx func s n r /\ exit_result r ==>
    !fuel. mem_safe_run fuel ctx func s
Proof
  rpt gen_tac >> strip_tac >>
  drule gas_path_mem_exec >> strip_tac >> gvs[exit_result_def] >>
  irule mem_safe_run_all_fuel >> qexists_tac `fuel` >>
  metis_tac[exit_result_not_error]
QED

(* From an exit along a memory path from an __entry block start, the
   entry's blocks run memory-safe at every fuel: the run reaches an exit,
   so the start block exists, and it has no phis. *)
Theorem lower_vyper_runtime_unit_exit_mem_safe_blocks:
  !tops rpolicy unit func s n r.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    ~ctx_has_dalloca unit.cu_context /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    s.vs_inst_idx = 0 /\
    gas_path_mem unit.cu_context func s n r /\ exit_result r ==>
    !fuel. mem_safe_blocks fuel unit.cu_context func s
Proof
  rpt gen_tac >> strip_tac >>
  drule_all gas_path_mem_exit_mem_safe_run >> strip_tac >>
  drule gas_path_mem_exec >> strip_tac >> gvs[exit_result_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by
    (Cases_on `lookup_block s.vs_current_bb func.fn_blocks` >>
     gvs[run_from_def, exit_result_def]) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[lower_vyper_runtime_unit_block_phi] >>
  `s with vs_inst_idx := 0 = s` by
    simp[venomStateTheory.venom_state_component_equality] >>
  irule mem_safe_blocks_no_phi >> asm_rewrite_tac[] >>
  qexists_tac `bb` >> simp[eval_phis_no_phi]
QED

Theorem source_unit_exit_safe_runs:
  !marks tops ret am tx unit vs rpolicy.
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    ~ctx_has_dalloca unit.cu_context /\
    source_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    call_outcomes_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    ~source_exempt tops
      (call_external (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings) am tx)
    ==>
    ?func (H : (bool # bytes32 # type_value) list # num list).
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      (!fuel. mem_safe_blocks fuel unit.cu_context func
         (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0 |>)) /\
      (!fuel. ptr_safe_blocks
         (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
         0 fuel unit.cu_context func [] FEMPTY entry_taint
         (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                     vs_inst_idx := 0 |>))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_unit_execution_correct_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_unit_execution_correct_at_def])
  >- (qpat_x_assum `!tail. ~_` (qspec_then `[]` mp_tac) >> gvs[])
  >- (qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      drule call_external_trace_result >> strip_tac >> gvs[]) >>
  qexistsl_tac [`func`, `storage_trace_horizon obs`] >> simp[] >>
  reverse conj_tac
  >- (first_x_assum (qspec_then `storage_trace_horizon obs` mp_tac) >>
      fs[storage_trace_domain_def]) >>
  drule gas_origin_path_erase >> simp[gas_marked_path_def] >> strip_tac >>
  irule lower_vyper_runtime_unit_exit_mem_safe_blocks >> simp[] >>
  metis_tac[]
QED

(* At every valid horizon of the certificate's own source trace, the run
   from the entry is pointer-safe at that horizon's dead set. *)
Theorem source_unit_exit_ptr_safe_horizons:
  !marks tops ret am tx unit vs func.
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    source_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    call_outcomes_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    ~source_exempt tops
      (call_external (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings) am tx)
    ==>
    !H. valid_horizon
          (initial_evaluation_context am.sources am.layouts tx NONE)
          (initial_state am []) H
          (source_storage_trace am tx vs.vs_outcomes
             (gas_explicit marks vs.vs_gas_readings)) ==>
        !fuel. ptr_safe_blocks
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 fuel unit.cu_context func [] FEMPTY entry_taint
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                      vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_unit_execution_correct_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [source_unit_execution_correct_at_def])
  >- (qpat_x_assum `!tail. ~_` (qspec_then `[]` mp_tac) >> gvs[])
  >- (qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
        (qspec_then `[]` assume_tac) >> fs[] >>
      drule call_external_trace_result >> strip_tac >> gvs[]) >>
  qpat_x_assum `!tail. call_external_trace _ _ _ _ = _`
    (qspec_then `[]` assume_tac) >>
  gvs[source_storage_trace_def]
QED

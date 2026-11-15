(* S3 for arbitrary calldata, from the joint entry-run certificates. *)
Theory loweringCalldataCorrect
Ancestors
  e2eDefs vyperLoweringCorrect loweringMemCorrect sourceUnitExecution
  sourceUnitExitSafe ptrDiscipline

(* S3 at the marks of S1's certificate (lower_vyper_runtime_unit_correct_dispatched),
   where the storage guards hold and the source call is not exempt: its exit
   arm gives the memory-safe run from the entry and, at every valid horizon
   of the source trace, the pointer-safe run at that horizon's dead set. *)
Theorem lower_vyper_runtime_unit_memory_ok_dispatched:
  !marks tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    initial_venom_state_rel tops am tx vs /\
    ~ctx_has_dalloca unit.cu_context /\
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    source_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    call_outcomes_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    ~source_exempt tops
      (call_external (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings) am tx)
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        !H. valid_horizon
              (initial_evaluation_context am.sources am.layouts tx NONE)
              (initial_state am []) H
              (source_storage_trace am tx vs.vs_outcomes
                 (gas_explicit marks vs.vs_gas_readings)) ==>
            taint_within
              (cx_dead H
                 (initial_evaluation_context am.sources am.layouts tx NONE))
              unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all source_unit_exit_safe_runs >> strip_tac >>
  qspecl_then [`marks`, `tops`, `ret`, `am`, `tx`, `unit`, `vs`, `func`]
    mp_tac source_unit_exit_ptr_safe_horizons >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  drule_all lower_vyper_runtime_unit_memory_ok >> strip_tac >>
  simp[] >> rpt strip_tac >>
  first_x_assum (drule_then assume_tac) >>
  drule_all lower_vyper_runtime_unit_memory_ok >> simp[]
QED

(* S3, calldata that dispatches to nothing, from the revert run of
   lower_vyper_runtime_unit_reverts: a memory path from the entry to the
   revert, and the pointer-safe run at every dead set. *)
Theorem lower_vyper_runtime_unit_reverts_memory_ok:
  !tops rpolicy unit am tx vs func s.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    initial_venom_state_rel tops am tx vs /\
    ~ctx_has_dalloca unit.cu_context /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    gas_path_mem unit.cu_context func
      (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                  vs_inst_idx := 0 |>) 0 (Abort Revert_abort s) /\
    (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY
                entry_taint
                (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0 |>))
    ==> raw_unit_memory_ok unit.cu_context vs /\
        EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
        fixed_region_reserved 0 unit.cu_context /\
        ptr_discipline 0 unit.cu_context vs /\
        ?D. dead_wf D /\ taint_within D unit.cu_context vs /\
        (code_layout_valid vs ==> mem_inv dload_offset_ok unit.cu_context vs) /\
        (code_layout_valid vs ==>
         mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                                  s.vs_code = vs.vs_code /\
                                  s.vs_data_section = vs.vs_data_section)
           unit.cu_context vs)
Proof
  rpt gen_tac >> strip_tac >>
  `!fuel. mem_safe_blocks fuel unit.cu_context func
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                        vs_inst_idx := 0 |>)` by
    (irule lower_vyper_runtime_unit_exit_mem_safe_blocks >> simp[] >>
     metis_tac[fragExecTheory.exit_result_def]) >>
  qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `vs`, `func`,
               `"__entry"`,
               `<| d_stor := (\a st. {}); d_trans := (\a st. {});
                   d_imm := K {}; d_ret := K {} |>`] mp_tac
    lower_vyper_runtime_unit_memory_ok >>
  impl_tac >- simp[] >> strip_tac >> simp[] >>
  qexists_tac `<| d_stor := (\a st. {}); d_trans := (\a st. {});
                 d_imm := K {}; d_ret := K {} |>` >>
  simp[dead_wf_def] >>
  metis_tac[lower_vyper_runtime_unit_dload_offset_ok,
            lower_vyper_runtime_unit_dload_in_section]
QED

(* DLOAD offsets stay within the data section, at the marks of S1's
   certificate as in lower_vyper_runtime_unit_memory_ok_dispatched. *)
Theorem lower_vyper_runtime_unit_dload_offset_ok_dispatched:
  !marks tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    code_layout_valid vs /\
    ~ctx_has_dalloca unit.cu_context /\
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    source_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    call_outcomes_storage_ok am tx vs.vs_outcomes
      (gas_explicit marks vs.vs_gas_readings) /\
    ~source_exempt tops
      (call_external (SOME vs.vs_outcomes)
         (gas_explicit marks vs.vs_gas_readings) am tx)
    ==> mem_inv dload_offset_ok unit.cu_context vs /\
        mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
                                 s.vs_code = vs.vs_code /\
                                 s.vs_data_section = vs.vs_data_section)
          unit.cu_context vs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all source_unit_exit_safe_runs >> strip_tac >>
  metis_tac[lower_vyper_runtime_unit_dload_offset_ok,
            lower_vyper_runtime_unit_dload_in_section]
QED

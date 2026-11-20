(* S1 and S3 for arbitrary calldata, with joint entry-run certificates. *)
Theory loweringCalldataCorrect
Ancestors
  e2eDefs vyperLoweringCorrect loweringMemCorrect sourceUnitExecution
  sourceUnitExitSafe ptrDiscipline vyperCalldata
  dispatchedCallAssembly dispatchedSelectedEndpoint gasShadowRunLowering
  loweringShapeProps calldataNoneEntryController calldataNoneDecoder acceptedContextPhi

(* The call a contract makes of raw calldata: the external entry it
   dispatches to and the arguments it decodes (vyperCalldata), including the
   __default__ fallback and noncanonical encodings. *)
Definition dispatched_vyper_call_def:
  dispatched_vyper_call tops tx calldata ret <=>
    calldata_dispatch tops calldata = SOME (tx.function_name, tx.args) /\
    ?mut nr args dflts body.
      vyperInterpreter$lookup_function NONE tx.function_name External tops =
        SOME (mut, nr, args, dflts, ret, body)
End

(* A supported program declares no default arguments, so every external
   entry it exposes (functions and public getters) has none. *)
(* S1 *)
(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  rpt gen_tac >> strip_tac >>
  `?shadow_unit. runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     drule supported_program_no_external_defaults >> simp[] >> strip_tac >>
     drule_at (Pat `classify_functions _ = _`) runtime_gas_shadow_unit_exists >>
     disch_then (drule_at (Pat `lower_vyper_runtime_unit _ _ = _`)) >>
     simp[] >> strip_tac >> qexists_tac `shadow_unit` >> simp[]) >>
  qpat_x_assum `dispatched_vyper_call _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dispatched_vyper_call_def]) >>
  drule_all_then SUBST_ALL_TAC supported_program_external_dflts_nil >>
  drule_at (Pat `runtime_gas_shadow_unit _ _ = _`)
    (cj 1 dispatched_call_correct) >>
  disch_then (drule_at (Pat `vyperInterpreter$lookup_function _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`unit`, `am`, `vs`] mp_tac) >>
  simp[]
QED
*)
Theorem lower_vyper_runtime_unit_correct_dispatched:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes)
    ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  cheat
QED

(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  rpt gen_tac >> strip_tac >>
  `?shadow_unit. runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     drule supported_program_no_external_defaults >> simp[] >> strip_tac >>
     drule_at (Pat `classify_functions _ = _`) runtime_gas_shadow_unit_exists >>
     disch_then (drule_at (Pat `lower_vyper_runtime_unit _ _ = _`)) >>
     simp[] >> strip_tac >> qexists_tac `shadow_unit` >> simp[]) >>
  qpat_x_assum `dispatched_vyper_call _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dispatched_vyper_call_def]) >>
  drule_all_then SUBST_ALL_TAC supported_program_external_dflts_nil >>
  drule_at (Pat `runtime_gas_shadow_unit _ _ = _`)
    dispatched_call_correct_with_readings >>
  disch_then (drule_at (Pat `vyperInterpreter$lookup_function _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`unit`, `am`, `vs`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `marks` >>
  metis_tac[source_unit_execution_correct_at_def]
QED
*)
Theorem lower_vyper_runtime_unit_correct_dispatched_readings_available:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes)
    ==>

    ?marks.
      source_unit_execution_correct_at marks tops ret am tx unit vs /\
      ((?tail.
          call_storage_ok am tx vs.vs_outcomes
            (gas_explicit marks vs.vs_gas_readings ++ tail)) ==>
       !tail.
         FST (call_external (SOME vs.vs_outcomes)
           (gas_explicit marks vs.vs_gas_readings ++ tail) am tx) <>
         INR (Error (RuntimeError "msg.gas: no gas reading")))
Proof
  cheat
QED

(* The dispatched-calldata unit theorem with a shadow context fixed by
   the program before the call, at the raw unit's own free-memory pointer. *)
(* TEMPORARILY CHEATED - SCRATCH SEQ-8501 census (never lands)
Proof
  rpt gen_tac >> strip_tac >>
  `?shadow_unit. runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit` by
    (Cases_on `classify_functions tops` >> PairCases_on `r` >>
     drule supported_program_no_external_defaults >> simp[] >> strip_tac >>
     drule_at (Pat `classify_functions _ = _`) runtime_gas_shadow_unit_exists >>
     disch_then (drule_at (Pat `lower_vyper_runtime_unit _ _ = _`)) >>
     simp[] >> strip_tac >> qexists_tac `shadow_unit` >> simp[]) >>
  qexists_tac `shadow_unit.cu_context` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `dispatched_vyper_call _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [dispatched_vyper_call_def]) >>
  drule_all_then SUBST_ALL_TAC supported_program_external_dflts_nil >>
  drule_at (Pat `runtime_gas_shadow_unit _ _ = _`)
    (cj 2 dispatched_call_correct) >>
  disch_then (drule_at (Pat `vyperInterpreter$lookup_function _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`unit`, `am`, `vs`] mp_tac) >>
  simp[]
QED
*)
Theorem lower_vyper_runtime_unit_correct_dispatched_with:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops ==>
    ?shadow_ctx. !am tx ret vs.
      source_typing_ok tops am tx /\
      source_deployment_rel tops am tx /\
      dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
      LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 /\
      initial_venom_state_rel tops am tx vs /\
      outcomes_accounts_typed (SOME vs.vs_outcomes) /\
      LENGTH vs.vs_outcomes < 2 ** 64 /\
      vs.vs_fmp = vs.vs_initial_fmp /\
      w2n vs.vs_initial_fmp < 2 ** 254 /\
      unit_alloca_budget unit.cu_context +
        32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp ==>
      ?marks.
        source_unit_execution_correct_with shadow_ctx marks
          tops ret am tx unit vs
Proof
  cheat
QED

(* S1, calldata that dispatches to nothing: no fallback, a short head, or a
   failed decode.  The entry reverts with empty returndata before any
   function body runs. *)
Theorem lower_vyper_runtime_unit_reverts:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    calldata_dispatch tops vs.vs_call_ctx.cc_calldata = NONE /\
    initial_venom_state_rel tops am tx vs
    ==>
    ?func s G' tn'.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      s.vs_returndata = [] /\
      (?fuel. run_context fuel unit.cu_context vs = Abort Revert_abort s) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (Abort Revert_abort s) /\
      (!D. gas_path_ptr D 0 unit.cu_context func [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>) 0 G' tn' (Abort Revert_abort s)) /\
      (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
                  (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                              vs_inst_idx := 0 |>))
Proof
  rpt gen_tac >> strip_tac >>
  drule none_entry_reject_from_decoder >>
  disch_then (drule_at (Pat `source_typing_ok _ _ _`)) >>
  disch_then (drule_at (Pat `initial_venom_state_rel _ _ _ _`)) >>
  disch_then irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `!bb. venomInst$lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all lower_vyper_runtime_unit_block_phi >> simp[]) >>
  drule (BETA_RULE none_coherent_decode_paths) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) o
    Q.INST [`limit` |-> `last`, `lo` |-> `0`, `PG` |-> `[]`] o SPEC_ALL) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspec_then `p` mp_tac) >>
  (impl_tac >-
    (simp[allocas_from_def] >> rpt gen_tac >> strip_tac >>
     qpat_assum `!id. first.cs_next_id <= id ==> _`
       (drule_then (fs o single)))) >>
  metis_tac[]
QED

(* S3 at the marks of S1's certificate (lower_vyper_runtime_unit_correct_dispatched),
   where the storage guards hold and the source call is not exempt: its exit
   arm gives the memory-safe run from the entry and, at every valid horizon
   of the source trace, the pointer-safe run at that horizon's dead set. *)
Theorem lower_vyper_runtime_unit_memory_ok_dispatched:
  !marks tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    initial_venom_state_rel tops am tx vs /\
    ~ctx_has_dalloca unit.cu_context /\
    w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    call_storage_ok am tx vs.vs_outcomes
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
    w2n vs.vs_initial_fmp <= w2n vs.vs_fmp /\
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
    call_storage_ok am tx vs.vs_outcomes
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

Theory loweringRuntimeBudgetAssembly
Ancestors
  loweringRuntimeBudgetShape sourceCallCount sourceCallCountEntryReplay
  sourceCallCountMonotone sourceCallCountWitness

Theorem lower_vyper_runtime_unit_call_budget_from_count:
  !tops rpolicy unit am tx ret vs k.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    k <= 2 ** 64 /\
    (!obs. source_calls_within k am tx vs.vs_outcomes obs) /\
    (!marks.
      source_storage_ok am tx vs.vs_outcomes
        (gas_explicit marks vs.vs_gas_readings) /\
      call_outcomes_storage_ok am tx vs.vs_outcomes
        (gas_explicit marks vs.vs_gas_readings)) /\
    (!marks. ~source_exempt tops
      (call_external (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings) am tx)) /\
    vs.vs_fmp = vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 ==>
    !D lo explicit name fn lbl entered p h marks q.
      unit.cu_context.ctx_entry = SOME name /\
      lookup_function name unit.cu_context.ctx_functions = SOME fn /\
      fn_entry_label fn = SOME lbl /\
      enters_block fn
        (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) entered /\
      p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
             bp_taint := entry_taint; bp_fn := fn; bp_state := entered |> /\
      lower_budget_path F (D,lo,explicit,unit.cu_context) p h marks q /\
      lower_history_count h <= k ==>
      ?remaining pair.
        remaining <= k /\ remaining <= 2 ** 64 /\
        lower_history_count h + remaining = k /\
        LENGTH (FILTER lower_event_allocates h) <= k /\
        (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
          SUC (LENGTH (FILTER lower_event_allocates h)) <= k) /\
        lower_history_pairs h pair /\ lower_history_current h pair q /\
        (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
          ?f i s op sz t. lower_alloc_record h n f i s op sz t)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all supported_runtime_budget_allocation_shape >> strip_tac >>
  qexistsl_tac [`k - lower_history_count h`, `pair`] >>
  simp[] >> conj_tac >- (fs[] >> decide_tac) >> metis_tac[]
QED

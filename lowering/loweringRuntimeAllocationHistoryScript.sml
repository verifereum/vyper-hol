(* The call-budget producer is an explicit hypothesis until its proof lands. *)
Theory loweringRuntimeAllocationHistory
Ancestors
  loweringCallBudgetHistory loweringJointPrefixHistory vyperLoweringCorrect
  loweringBudgetActualShadow loweringBudgetCompilerCuts
  loweringBudgetMarkedResidual loweringBudgetOracleConsumption
  loweringBudgetOraclePrefix loweringBudgetPathDeterminism
  loweringBudgetPrecompilePrefix loweringBudgetResidualArithmetic
  loweringBudgetReturnStorePrefix loweringBudgetSourceResidual
  loweringBudgetTerminalFrontier loweringRuntimeBudgetAssembly
  loweringBudgetExitCoverage
  loweringRuntimeBudgetSourceEntry
  ptrDiscipline contextRawReachable sourceCallCount compileVyper
  vyperCompiler e2eDefs lowerDloadDefs o1PassContract
  list arithmetic

Theorem lower_vyper_runtime_unit_allocation_history:
  (!tops rpolicy unit am tx ret vs k.
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
      lower_budget_path F (D,lo,explicit,unit.cu_context) p h marks q ==>
      ?remaining pair.
        remaining <= k /\ remaining <= 2 ** 64 /\
        lower_history_count h + remaining = k /\
        LENGTH (FILTER lower_event_allocates h) <= k /\
        (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
          SUC (LENGTH (FILTER lower_event_allocates h)) <= k) /\
        lower_history_pairs h pair /\ lower_history_current h pair q /\
        (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
          ?f i s op sz t. lower_alloc_record h n f i s op sz t)) ==>
  (!tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    (!obs. source_calls_within (2 ** 64) am tx vs.vs_outcomes obs) /\
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
    !f i s D lo explicit.
      raw_reachable vs unit.cu_context f i s ==>
      ?name fn lbl entered p h marks q pair remaining.
        unit.cu_context.ctx_entry = SOME name /\
        lookup_function name unit.cu_context.ctx_functions = SOME fn /\
        fn_entry_label fn = SOME lbl /\
        enters_block fn
          (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                      vs_inst_idx := 0 |>) entered /\
        p = <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
               bp_taint := entry_taint; bp_fn := fn; bp_state := entered |> /\
        lower_budget_path F (D,lo,explicit,unit.cu_context) p h marks q /\
        q.bp_fn = f /\ q.bp_state = s /\ active_inst f i s /\
        lower_history_count h + remaining = 2 ** 64 /\
        LENGTH (FILTER lower_event_allocates h) <= 2 ** 64 /\
        (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
          SUC (LENGTH (FILTER lower_event_allocates h)) <= 2 ** 64) /\
        lower_history_pairs h pair /\ lower_history_current h pair q /\
        (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
          ?af ai pre op sz post.
            lower_alloc_record h n af ai pre op sz post))
Proof
  disch_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `~vs.vs_halted` by fs[initial_venom_state_rel_def] >>
  qspecl_then [`vs`, `unit.cu_context`, `f`, `i`, `s`,
                `D`, `lo`, `explicit`] mp_tac lower_budget_raw_history >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `!tops rpolicy unit am tx ret vs k. _`
    (qspecl_then [`tops`, `rpolicy`, `unit`, `am`, `tx`, `ret`,
                  `vs`, `2 ** 64`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`D`, `lo`, `explicit`, `name`, `entry`,
    `lbl`, `entered`, `p`, `h`, `marks`, `q`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`name`, `entry`, `lbl`, `entered`, `p`, `h`,
                `marks`, `q`, `pair`, `remaining`] >>
  simp[] >>
  qpat_x_assum `!i. active_inst q.bp_fn i q.bp_state /\ _ ==> _` mp_tac >>
  simp[]
QED


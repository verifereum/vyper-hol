(* Guarded runtime body continuation: the selected joint execution and its
   quantitative recorder share marks, horizon and terminal endpoint.
   The source horizon permits one unmatched terminal precompile effect;
   it does not assert nonempty target outcomes on every abort. *)
Theory loweringBudgetBodyBridge
Ancestors
  loweringCallBudgetHistory bodySimFullMain bodySimFull
  externalEntryJoint externalBodyFrame externalFrameRetOk runtimeBodyShadow
  externalCallSelected externalBodySourceOk unitExecutionCompose
  loweringJointPrefixHistory loweringRuntimeBudgetShape
  loweringBudgetExitCoverage loweringBudgetRecorderOutcomes
  loweringBudgetResidualArithmetic loweringBudgetOracleConsumption
  loweringBudgetPrecompilePrefix loweringBudgetMarkedResidual
  sourceCallCount sourceCallCountEntryReplay sourceCallCountMonotone
  sourceCallCountWitness sourceUnitExecution e2eDefs compileVyper
  vyperLoweringCorrect vyperCompiler gasOutcomeFull gasExplicitSites
  fragGasOriginPtr ptrDiscipline ptrSafeRun list rich_list arithmetic pred_set

Theorem lower_vyper_runtime_unit_joint_prefix_history:
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
    ?shadow_ctx func shadow_func certificates marks.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      (((!tail.
           ~(source_storage_ok am tx vs.vs_outcomes
               (gas_explicit marks vs.vs_gas_readings ++ tail) /\
             call_outcomes_storage_ok am tx vs.vs_outcomes
               (gas_explicit marks vs.vs_gas_readings ++ tail))) /\
        ?(H : (bool # bytes32 # type_value) list # num list)
           leaf leaf_pg leaf_g leaf_tn finish.
          (?h_cert. (H,h_cert,marks,
              INL (leaf,leaf_pg,leaf_g,leaf_tn,finish)) IN certificates)) \/
       ?res am' rqs obs.
         (!tail. call_external_trace (SOME vs.vs_outcomes)
            (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
            (res, am', rqs, obs)) /\
         ((source_exempt tops (res, am', rqs) /\
           ?(H : (bool # bytes32 # type_value) list # num list)
              leaf leaf_pg leaf_g leaf_tn finish.
             (?h_cert. (H,h_cert,marks,
              INL (leaf,leaf_pg,leaf_g,leaf_tn,finish)) IN certificates)) \/
          (?r. exit_result r /\
             storage_trace_domain
               (initial_evaluation_context am.sources am.layouts tx NONE)
               (initial_state am []) obs /\
             !H. valid_horizon
                   (initial_evaluation_context am.sources am.layouts tx NONE)
                   (initial_state am []) H obs ==>
               (?h_cert G' tn'. (H,h_cert,marks,INR (r,G',tn')) IN certificates) /\
               external_call_result_rel H tops ret tx (res, am', rqs) r /\
               (!fuel. ptr_safe_blocks
                 (cx_dead H
                   (initial_evaluation_context am.sources am.layouts tx NONE))
                 0 fuel unit.cu_context func [] FEMPTY entry_taint
                 (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                             vs_inst_idx := 0 |>))))) /\
      (!H h_cert cert_marks out.
        (H,h_cert,cert_marks,out) IN certificates ==>
        lower_budget_certificate
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
           0,gas_explicit_sites unit.cu_context shadow_ctx,unit.cu_context)
          <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
                   bp_taint := entry_taint; bp_fn := func;
                   bp_state := (vs with <| vs_prev_bb := NONE;
                     vs_current_bb := "__entry"; vs_inst_idx := 0 |>) |> h_cert cert_marks out /\
        !h marks' q.
          lower_budget_path T
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
             0,gas_explicit_sites unit.cu_context shadow_ctx,unit.cu_context)
            <| bp_stack := []; bp_params := []; bp_prov := FEMPTY;
                   bp_taint := entry_taint; bp_fn := func;
                   bp_state := (vs with <| vs_prev_bb := NONE;
                     vs_current_bb := "__entry"; vs_inst_idx := 0 |>) |> h marks' q /\
          IS_PREFIX h_cert h ==>
          ?remaining pair.
            lower_history_count h + remaining = k /\
            LENGTH (FILTER lower_event_allocates h) <= k /\
            (!i. active_inst q.bp_fn i q.bp_state /\ i.inst_opcode = DALLOCA ==>
              SUC (LENGTH (FILTER lower_event_allocates h)) <= k) /\
            lower_history_pairs h pair /\ lower_history_current h pair q /\
            (!n. n < LENGTH h /\ lower_event_allocates (EL n h) ==>
              ?af ai pre op sz post.
                lower_alloc_record h n af ai pre op sz post))
Proof
  FAIL_TAC "Unproved additive causal body refinement"
QED


(* Shared premises for the call-side gas links. *)
Theory e2eOutcomesDefs
Ancestors
  e2eDefs sourceUnitExecution vyperLoweringCorrect supportedProgram compileVyper
  vyperRequestTrace vyperStorageFootprint extCallOracle vyperInterpreter
  callTrace vfmExecution venomExecSemantics ptrDiscipline unitMemInv lowerDloadDefs
  sourceCallCount e2eProducers asmOptimizer

Definition vyper_call_staging_def:
  vyper_call_staging fin policy tops runtime_bc am tx ret es <=>
    fin IN accepted_finalizers /\
    (fin = asm_opt_finalizer ==> ~program_reads_self_code tops) /\
    (?deploy_bc. compile_vyper fin policy tops = SOME (deploy_bc, runtime_bc)) /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    (!obs. source_calls_within (2 ** 64) am tx
             (MAP SND (call_trace es)) obs)
End

Definition s1_request_prefix_def:
  s1_request_prefix tops <=>
    !rpolicy unit.
      lower_vyper_runtime_unit tops rpolicy = SOME unit /\
      supported_program tops ==>
      ?shadow_ctx. !am tx ret vs.
        source_typing_ok tops am tx /\
        source_deployment_rel tops am tx /\
        valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
        initial_venom_state_rel tops am tx vs /\
        code_layout_valid vs /\
        EVERY (\oc. LENGTH oc.co_returnData < dimword(:256) /\
                    accounts_runtime_well_typed oc.co_accounts) vs.vs_outcomes /\
        (!obs. source_calls_within (2 ** 64) am tx vs.vs_outcomes obs) /\
        vs.vs_fmp = vs.vs_initial_fmp /\
        w2n vs.vs_initial_fmp < 2 ** 254 /\
        unit_alloca_budget unit.cu_context +
          32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp ==>
        ?marks.
          source_unit_execution_correct_with shadow_ctx marks
            tops ret am tx unit vs /\
          !tail res am' rqs obs obs_pre rq outcome sfx H.
            call_external_trace (SOME vs.vs_outcomes)
              (gas_explicit marks vs.vs_gas_readings ++ tail) am tx =
              (res,am',rqs,obs) /\
            ~source_exempt tops (res,am',rqs) /\
            obs = obs_pre ++ StorageOutcome rq outcome :: sfx /\
            valid_horizon
              (initial_evaluation_context am.sources am.layouts tx NONE)
              (initial_state am []) H obs_pre ==>
            raw_unit_memory_ok unit.cu_context vs /\
            ptr_discipline 0 unit.cu_context vs /\
            taint_within
              (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
              unit.cu_context vs /\
            mem_inv dload_offset_ok unit.cu_context vs /\
            ?fuel ss.
              (run_context fuel unit.cu_context vs = Halt ss \/
               ?a. run_context fuel unit.cu_context vs = Abort a ss) /\
              (computed_precompile rq ==>
                 outcome.co_accounts = rq.cr_accounts /\
                 outcome.co_tStorage = rq.cr_tStorage) /\
              (~computed_precompile rq ==>
                 recorded_outcomes_count obs_pre < LENGTH rqs /\
                 recorded_outcomes_count obs_pre < LENGTH ss.vs_requests /\
                 EL (recorded_outcomes_count obs_pre) rqs = rq /\
                 request_agree H tx.target
                   rq (EL (recorded_outcomes_count obs_pre) ss.vs_requests) /\
                 (outcome = failed_outcome rq \/
                  recorded_outcomes_count obs_pre < LENGTH vs.vs_outcomes /\
                  outcome = EL (recorded_outcomes_count obs_pre) vs.vs_outcomes))
End

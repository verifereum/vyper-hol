(*
 * Closed-world producer of the storage guard on callee outcomes.
 *
 * call_result_rel guards call_result_rel_at by call_outcomes_storage_ok: the
 * contract's storage backends the source run adopts from call outcomes are
 * well formed on the run's own horizon.  When every re-entry into the
 * contract during the call is itself a call to the same compiled contract,
 * on one storage horizon H shared with the caller, the guard holds and
 * closed_world_call_outcomes_ok concludes the call theorem without it.
 *
 * The S1 request-prefix companion (the first i source requests agree with
 * the lowered run's while the trace up to the i-th outcome is a valid
 * horizon) is carried as the premise s1_request_prefix until the lowering
 * proof provides it.
 *
 * TOP-LEVEL: closed_world_call_outcomes_ok
 *)
Theory e2eOutcomesProducer
Ancestors
  e2eDefs vyperLoweringCorrect gasSummary compileVyper loweringShapeProps
  supportedProgram callTrace frameOutcome extCallOracle vyperStorageFootprint
  vyperRuntimeAccounts vyperInterpreter venomExecSemantics vyperRequestTrace
  vfmAccountFrame vfmExecution

(* The call theorem's premises other than its storage guards, for one call
   frame es of the compiled contract.  Re-entries meet the same premises. *)
Definition vyper_call_staging_def:
  vyper_call_staging policy tops runtime_bc am tx ret es <=>
    (?deploy_bc. compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc)) /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx
      (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret
End

(* The S1 request-prefix companion.  One gas marking, chosen without the
   storage guard on callee outcomes, serves both conjuncts: S1 under its
   storage guards, and agreement of the first i source requests with the
   lowered run's wherever the source trace up to the i-th recorded outcome
   is a valid horizon for H. *)
Definition s1_request_prefix_def:
  s1_request_prefix tops <=>
    !rpolicy unit am tx ret vs.
      lower_vyper_runtime_unit tops rpolicy = SOME unit /\
      supported_program tops /\ source_typing_ok tops am tx /\
      source_deployment_rel tops am tx /\
      valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
      initial_venom_state_rel tops am tx vs /\
      EVERY (\oc. LENGTH oc.co_returnData < dimword(:256) /\
                  accounts_runtime_well_typed oc.co_accounts) vs.vs_outcomes ==>
      ?marks.
        (source_storage_ok am tx vs.vs_outcomes
           (gas_explicit marks vs.vs_gas_readings) /\
         call_outcomes_storage_ok am tx vs.vs_outcomes
           (gas_explicit marks vs.vs_gas_readings) ==>
         source_unit_execution_correct_at (gas_explicit marks vs.vs_gas_readings)
           tops ret am tx unit vs) /\
        !fuel ss res am' rqs obs obs_pre sfx H.
          (run_context fuel unit.cu_context vs = Halt ss \/
           ?a. run_context fuel unit.cu_context vs = Abort a ss) /\
          call_external_trace (SOME vs.vs_outcomes)
            (gas_explicit marks vs.vs_gas_readings) am tx = (res,am',rqs,obs) /\
          ~source_exempt tops (res,am',rqs) /\
          obs = obs_pre ++ sfx /\
          valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
            (initial_state am []) H obs_pre ==>
          recorded_outcomes_count obs_pre <= LENGTH rqs /\
          recorded_outcomes_count obs_pre <= LENGTH ss.vs_requests /\
          LIST_REL
            (request_agree H (initial_evaluation_context am.sources am.layouts tx NONE))
            (TAKE (recorded_outcomes_count obs_pre) rqs)
            (TAKE (recorded_outcomes_count obs_pre) ss.vs_requests)
End

(* H holds every region and lock of the call's source trace, whatever gas
   observations it reads. *)
Definition horizon_covers_def:
  horizon_covers H am tx os <=>
    !gobs.
      EVERY (\r. MEM r (FST H))
        (storage_trace_regions (source_storage_trace am tx os gobs)) /\
      EVERY (\l. MEM l (SND H))
        (storage_trace_locks (source_storage_trace am tx os gobs)) /\
      storage_roots_fit (source_storage_trace am tx os gobs)
End

(* One horizon H for the caller and every re-entry into it during es's run.
   A re-entry is a non-static frame executing as tx.target pushed by a step
   reachable from es; it must be a call to the same compiled contract
   (vyper_call_staging, which pins its code to runtime_bc and needs no
   pending deletions), on the caller's sources and layouts, whose source
   call H covers and that never ends in an exempt error.  Static frames
   write nothing.  A delegatecall or callcode from the contract runs other
   code as tx.target, so the re-entry clause excludes it. *)
Definition vyper_closed_world_def:
  vyper_closed_world policy tops runtime_bc am tx H es <=>
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am []) (FST H) /\
    horizon_covers H am tx (MAP SND (call_trace es)) /\
    !s u e.
      run_call_reaches es s /\ step s = (INL u, e) /\
      LENGTH s.contexts < LENGTH e.contexts /\
      (FST (HD e.contexts)).msgParams.callee = tx.target /\
      ~(FST (HD e.contexts)).msgParams.static ==>
      ?am_e tx_e ret_e.
        am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
        vyper_call_staging policy tops runtime_bc am_e tx_e ret_e e /\
        horizon_covers H am_e tx_e (MAP SND (call_trace e)) /\
        !gobs. ~source_exempt tops
                 (call_external (SOME (MAP SND (call_trace e))) gobs am_e tx_e)
End

Theorem closed_world_call_outcomes_ok:
  !policy tops runtime_bc am tx ret es H.
    vyper_call_staging policy tops runtime_bc am tx ret es /\
    s1_request_prefix tops /\
    vyper_closed_world policy tops runtime_bc am tx H es ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       gas_readings_rel (gas_readings es)
         (\gobs.
            source_storage_ok am tx (MAP SND (call_trace es)) gobs ==>
            call_outcomes_storage_ok am tx (MAP SND (call_trace es)) gobs /\
            call_result_rel_at gobs tops ret am tx es r es') T)
Proof
  cheat
QED

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
 * The S1 request-prefix companion (while the trace up to the k-th recorded
 * outcome is a valid horizon, the lowered unit is memory safe, terminates,
 * and its k-th request agrees with the source's, whose outcome is the k-th
 * callee outcome) is carried as the premise s1_request_prefix until the
 * lowering proof provides it.
 *
 * TOP-LEVEL: closed_world_call_outcomes_ok
 *)
Theory e2eOutcomesProducer
Ancestors
  e2eDefs sourceUnitExecution vyperLoweringCorrect gasSummary compileVyper loweringShapeProps
  supportedProgram callTrace frameOutcome extCallOracle vyperStorageFootprint
  vyperRuntimeAccounts vyperInterpreter venomExecSemantics vyperRequestTrace
  vfmAccountFrame vfmExecution callTraceFrame unitTransformDefs ptrDiscipline
  unitMemInv lowerDloadDefs vyperCallStorageFootprint

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
   storage guard on callee outcomes, serves both conjuncts: S1's selected-run
   certificate (whose storage guards are inside it), and, at each recorded
   outcome whose preceding trace obs_pre is a valid horizon for H, the facts
   the Venom stages need up to that outcome (the raw unit's memory safety and
   a terminating run) and the alignment of that outcome with the k-th
   request (k = recorded_outcomes_count obs_pre) of both runs: the request
   agrees with the lowered run's, and its outcome is the k-th callee outcome
   or the request's failure. *)
Definition s1_request_prefix_def:
  s1_request_prefix tops <=>
    !rpolicy unit am tx ret vs.
      lower_vyper_runtime_unit tops rpolicy = SOME unit /\
      supported_program tops /\ source_typing_ok tops am tx /\
      source_deployment_rel tops am tx /\
      valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
      initial_venom_state_rel tops am tx vs /\
      code_layout_valid vs /\
      EVERY (\oc. LENGTH oc.co_returnData < dimword(:256) /\
                  accounts_runtime_well_typed oc.co_accounts) vs.vs_outcomes ==>
      ?marks.
        source_unit_execution_correct_at marks tops ret am tx unit vs /\
        !res am' rqs obs obs_pre rq outcome sfx H.
          call_external_trace (SOME vs.vs_outcomes)
            (gas_explicit marks vs.vs_gas_readings) am tx = (res,am',rqs,obs) /\
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
               request_agree H
                 (initial_evaluation_context am.sources am.layouts tx NONE)
                 rq (EL (recorded_outcomes_count obs_pre) ss.vs_requests) /\
               (outcome = failed_outcome rq \/
                recorded_outcomes_count obs_pre < LENGTH vs.vs_outcomes /\
                outcome = EL (recorded_outcomes_count obs_pre) vs.vs_outcomes))
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
   code as tx.target, so the re-entry clause excludes it.  The contract
   existed before the transaction, so no frame's self-destruct deletes it
   (run_call_to_delete), and the caller's call never ends in an exempt
   error either: the source adopts callee outcomes before it decodes.  No
   call into a computed precompile, so the k-th callee outcome answers the
   k-th recorded request. *)
Definition vyper_closed_world_def:
  vyper_closed_world policy tops runtime_bc am tx H es <=>
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) /\
    storage_well_formed_on (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am []) (FST H) /\
    horizon_covers H am tx (MAP SND (call_trace es)) /\
    ~account_empty (lookup_account tx.target es.originalAccounts) /\
    EVERY (\p. ~computed_precompile (FST p)) (call_trace es) /\
    (!gobs. ~source_exempt tops
              (call_external (SOME (MAP SND (call_trace es))) gobs am tx)) /\
    !s u e.
      run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts /\
      step s = (INL u, e) /\
      LENGTH s.contexts < LENGTH e.contexts /\
      (FST (HD e.contexts)).msgParams.callee = tx.target /\
      ~(FST (HD e.contexts)).msgParams.static ==>
      ?am_e tx_e ret_e.
        am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
        vyper_call_staging policy tops runtime_bc am_e tx_e ret_e e /\
        horizon_covers H am_e tx_e (MAP SND (call_trace e)) /\
        EVERY (\p. ~computed_precompile (FST p)) (call_trace e) /\
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

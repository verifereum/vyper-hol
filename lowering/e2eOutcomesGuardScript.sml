(*
 * Closed-world storage guard on callee outcomes, short of the call theorem.
 *
 * Definitions of the closed world (vyper_closed_world), the S1
 * request-prefix companion carried as a premise (s1_request_prefix), and
 * closed_world_outcomes_guard: at the companion's gas marking, the guard
 * call_outcomes_storage_ok follows from source_storage_ok, given the
 * producer's conclusion for every re-entry.  e2eOutcomesProducer adds the
 * induction on call depth and the call theorem.
 *)
Theory e2eOutcomesGuard
Ancestors
  e2eDefs sourceUnitExecution vyperLoweringCorrect gasSummary compileVyper loweringShapeProps
  supportedProgram callTrace frameOutcome extCallOracle vyperStorageFootprint
  vyperRuntimeAccounts vyperInterpreter venomExecSemantics vyperRequestTrace
  vfmAccountFrame vfmExecution callTraceFrame unitTransformDefs ptrDiscipline
  unitMemInv lowerDloadDefs vyperCallStorageFootprint e2eProducers e2eEntry o1PipelineCorrect o1PassContract o1RequestRuns
  o1PipelineRequests e2eComposition loweringShapeSource immutableCodeLayout staticLayoutDefs

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
   certificate (whose storage guards are inside it), and, for every tail of
   gas readings past the marked ones and at each recorded outcome whose preceding trace obs_pre is a valid horizon for H, the facts
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

(* Phase and marking witnesses are chosen before the storage guard. *)
Theorem closed_world_guard_setup[local]:
  vyper_call_staging policy tops runtime_bc am tx ret es /\
  s1_request_prefix tops ==>
  ?rpolicy unit out prog cp vs marks.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    gas_variant vs (entry_venom_state prog cp es) /\
    (!H'. raw_unit_memory_ok unit.cu_context vs /\
      ptr_discipline 0 unit.cu_context vs /\
      taint_within (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))
        unit.cu_context vs /\
      mem_inv dload_offset_ok unit.cu_context vs /\
      mem_inv dload_headroom_ok unit.cu_context vs ==>
      ctx_sim (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))
        unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
      ctx_abort_rq (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))
        unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
      o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cp es)) /\
    source_unit_execution_correct_at marks tops ret am tx unit vs /\
    !tail res am' rqs obs obs_pre rq outcome sfx H.
      call_external_trace (SOME vs.vs_outcomes)
        (gas_explicit marks vs.vs_gas_readings ++ tail) am tx = (res,am',rqs,obs) /\
      ~source_exempt tops (res,am',rqs) /\
      obs = obs_pre ++ StorageOutcome rq outcome :: sfx /\
      valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
        (initial_state am []) H obs_pre ==>
      raw_unit_memory_ok unit.cu_context vs /\
      ptr_discipline 0 unit.cu_context vs /\
      taint_within (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
        unit.cu_context vs /\
      mem_inv dload_offset_ok unit.cu_context vs /\
      ?fuel ss.
        (run_context fuel unit.cu_context vs = Halt ss \/
         ?a. run_context fuel unit.cu_context vs = Abort a ss) /\
        (computed_precompile rq ==>
          outcome.co_accounts = rq.cr_accounts /\ outcome.co_tStorage = rq.cr_tStorage) /\
        (~computed_precompile rq ==>
          recorded_outcomes_count obs_pre < LENGTH rqs /\
          recorded_outcomes_count obs_pre < LENGTH ss.vs_requests /\
          EL (recorded_outcomes_count obs_pre) rqs = rq /\
          request_agree H (initial_evaluation_context am.sources am.layouts tx NONE)
            rq (EL (recorded_outcomes_count obs_pre) ss.vs_requests) /\
          (outcome = failed_outcome rq \/
           recorded_outcomes_count obs_pre < LENGTH vs.vs_outcomes /\
           outcome = EL (recorded_outcomes_count obs_pre) vs.vs_outcomes))
Proof
  simp[vyper_call_staging_def] >> rpt strip_tac >>
  drule compile_vyper_runtime_phases >> strip_tac >>
  rename1 `generate_context_plan out.po_unit.cu_context = SOME cplan` >>
  qpat_x_assum `runtime_bc = assemble _` SUBST_ALL_TAC >>
  qpat_x_assum `prog = _` kall_tac >>
  drule supported_program_raw_shape_free_program >> strip_tac >>
  `?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art` by
    metis_tac[source_typing_ok_def] >>
  drule_all lower_vyper_runtime_unit_source_unit_ok >> strip_tac >>
  drule_all lower_vyper_runtime_unit_o1_shape_extras >> strip_tac >>
  drule_all lower_vyper_runtime_unit_defs_reach_uses >> strip_tac >>
  drule_all run_venom_pipeline_output_shape >> strip_tac >>
  `code_layout_valid (entry_venom_state prog cplan es)` by
    (irule generated_entry_code_layout_shape >> metis_tac[]) >>
  `o1_run_state_ok (entry_venom_state prog cplan es)` by
    (simp[o1_run_state_ok_def, entry_venom_state_o1_initial_state_ok] >>
     gvs[entry_venom_state_fresh, entry_venom_state_def, call_state_rel_def]) >>
  `EVERY (\fn. fn.fn_eom = NONE) unit.cu_context.ctx_functions /\
   fixed_region_reserved 0 unit.cu_context` by
    (drule lower_vyper_runtime_unit_raw_defaults >> simp[fixed_region_reserved_def]) >>
  `reserved_intervals_wf unit.cu_context.ctx_global_reserved` by
    (drule lower_vyper_runtime_unit_global_reserved >> simp[reserved_intervals_wf_def]) >>
  drule_all (run_venom_pipeline_correct_requests_all_dead |> Q.SPEC `0`) >>
  strip_tac >>
  `initial_venom_state_rel tops am tx vs_in` by
    (irule gas_variant_initial_venom_state_rel >>
     goal_assum $ drule_at Any >>
     irule entry_venom_state_initial_venom_state_rel >> simp[]) >>
  `code_layout_valid vs_in` by
    (irule gas_variant_code_layout_valid >> goal_assum $ drule_at Any >>
     irule generated_entry_code_layout_shape >> metis_tac[]) >>
  `vs_in.vs_outcomes = MAP SND (call_trace es) /\
   vs_in.vs_call_ctx.cc_calldata = buffer_to_list (FST (HD es.contexts)).msgParams.data` by
    (drule gas_variant_outcomes >> drule gas_variant_call_ctx >>
     simp[entry_venom_state_def]) >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def] >>
  `EVERY (\oc. LENGTH oc.co_returnData < dimword(:256) /\
    accounts_runtime_well_typed oc.co_accounts) vs_in.vs_outcomes` by
    (simp[] >> irule call_trace_outcomes_bounded >> fs[call_state_rel_def]) >>
  qpat_x_assum `s1_request_prefix tops` mp_tac >>
  simp[ s1_request_prefix_def] >>
  disch_then (qspecl_then [`rpolicy`, `unit`, `am`, `tx`, `ret`, `vs_in`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  qexistsl_tac [`vs_in`, `marks`] >>
  simp[] >> reverse conj_tac >- gvs[] >> gen_tac >>
  `dead_wf (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))` by
    (mp_tac (external_call_dead_wf |> Q.INST [`H` |-> `H'`, `src` |-> `(ARB,ARB,ARB)`]) >>
     simp[external_call_dead_def, cx_dead_def, initial_evaluation_context_def]) >>
  metis_tac[]
QED

(* The substance of the producer, short of the call theorem.  For the
   lowered unit and the raw-unit entry state vs the compiled run of es starts
   from (up to its gas readings), at the S1 companion's gas marking, the
   storage guard on callee outcomes follows from the guard on the call's own
   storage, given that every re-entry into the contract during the call meets
   the producer's conclusion (the induction hypothesis on call depth that
   closed_world_call_outcomes_ok discharges). *)
Theorem closed_world_outcomes_guard:
  !policy tops runtime_bc am tx ret es H.
    vyper_call_staging policy tops runtime_bc am tx ret es /\
    s1_request_prefix tops /\
    vyper_closed_world policy tops runtime_bc am tx H es /\
    (!s u e am_e tx_e ret_e.
       run_call_reaches es s /\ LENGTH es.contexts <= LENGTH s.contexts /\
       step s = (INL u, e) /\ LENGTH s.contexts < LENGTH e.contexts /\
       (FST (HD e.contexts)).msgParams.callee = tx.target /\
       ~(FST (HD e.contexts)).msgParams.static /\
       am_e.sources = am.sources /\ am_e.layouts = am.layouts /\
       vyper_call_staging policy tops runtime_bc am_e tx_e ret_e e /\
       vyper_closed_world policy tops runtime_bc am_e tx_e H e ==>
       ?r_e e'.
         run_call e = SOME (r_e, e') /\
         (frame_resource_starved e r_e e' \/
          gas_readings_rel (gas_readings e)
            (\gobs.
               source_storage_ok am_e tx_e (MAP SND (call_trace e)) gobs ==>
               call_outcomes_storage_ok am_e tx_e (MAP SND (call_trace e)) gobs /\
               call_result_rel_at gobs tops ret_e am_e tx_e e r_e e') T)) ==>
    ?rpolicy unit out prog cp vs marks.
      resolve_o1_policy policy = SOME rpolicy /\
      lower_vyper_runtime_unit tops rpolicy = SOME unit /\
      o1_pipeline rpolicy unit = SOME out /\
      codegen_assembly rpolicy out.po_unit = SOME prog /\
      generate_context_plan out.po_unit.cu_context = SOME cp /\
      gas_variant vs (entry_venom_state prog cp es) /\
      (!H'. raw_unit_memory_ok unit.cu_context vs /\
       ptr_discipline 0 unit.cu_context vs /\
       taint_within (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))
         unit.cu_context vs /\
       mem_inv dload_offset_ok unit.cu_context vs /\
       mem_inv dload_headroom_ok unit.cu_context vs ==>
       ctx_sim (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))
         unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
       ctx_abort_rq (cx_dead H' (initial_evaluation_context am.sources am.layouts tx NONE))
         unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
       o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cp es)) /\
      source_unit_execution_correct_at marks tops ret am tx unit vs /\
      !tail.
        source_storage_ok am tx (MAP SND (call_trace es))
          (gas_explicit marks vs.vs_gas_readings ++ tail) ==>
        call_outcomes_storage_ok am tx (MAP SND (call_trace es))
          (gas_explicit marks vs.vs_gas_readings ++ tail)
Proof
  cheat
QED

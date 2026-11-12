(*
 * vyper_call_correct_at_marks: the call theorem at one fixed gas marking.
 *
 * The caller supplies the raw-unit entry state vs (a gas variant of the
 * compiled run's entry state), the S4 simulation facts on it for every dead
 * mask, and S1's selected-run certificate at marks.  The conclusion is the
 * call result relation at every gas filling past the marked readings where
 * the storage guards hold.  Fixing marks lets a caller that chose them for
 * another purpose (the callee-outcome guard in e2eOutcomesGuard) use the
 * same filling; vyper_call_correct is this theorem plus the choice of vs
 * and marks.
 *)
Theory e2eCallAtMarks
Ancestors
  e2eDefs sourceUnitExecution e2eComposition vyperLoweringCorrect gasSummary compileVyper
  loweringShapeProps supportedProgram callTrace frameOutcome vyperInterpreter
  venomExecSemantics unitTransformDefs ptrDiscipline unitMemInv lowerDloadDefs
  e2eProducers e2eEntry o1PipelineCorrect o1PassContract codegenCorrectness
  vyperStorageFootprint loweredUnitMemoryFrontier fragGasPathMem fragExecMem

Theorem guarded_storage_horizon[local]:
  source_storage_ok am tx os gs /\ call_outcomes_storage_ok am tx os gs ==>
  valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [])
    (storage_trace_horizon (source_storage_trace am tx os gs))
    (source_storage_trace am tx os gs)
Proof
  simp[source_storage_ok_def, call_outcomes_storage_ok_def,
       valid_horizon_def, storage_observations_ok_def, storage_trace_horizon_def,
       listTheory.EVERY_MEM] >>
  rpt strip_tac >> simp[]
QED

Theorem call_at_horizon_composition[local]:
  run_call es = SOME (r, es') /\ ~frame_resource_starved es r es' /\
  external_call_result_rel
    (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gs))
    tops ret tx (call_external (SOME (MAP SND (call_trace es))) gs am tx)
    (run_context fuel ctx vs) /\
  ctx_sim
    (external_call_dead
      (storage_trace_horizon (source_storage_trace am tx (MAP SND (call_trace es)) gs))
      tx (call_external (SOME (MAP SND (call_trace es))) gs am tx))
    ctx ctx' vs vs' /\
  (!n. ?r' es''. run_call es = SOME (r', es'') /\
    (frame_resource_starved es r' es'' \/
     venom_frame_rel es r' es'' (run_context n ctx' vs'))) ==>
  call_result_rel_at gs tops ret am tx es r es'
Proof
  rpt strip_tac >>
  drule_all external_call_result_rel_terminates >> strip_tac >>
  qpat_x_assum `ctx_sim _ _ _ _ _` mp_tac >>
  simp[ctx_sim_def] >> disch_then drule >> strip_tac >>
  qpat_x_assum `!n. ?r' es''. _` (qspec_then `fuel'` strip_assume_tac) >>
  gvs[] >>
  drule_all external_call_result_rel_dead_transport >> strip_tac >>
  drule_all external_call_result_rel_frame >> simp[]
QED

Theorem vyper_call_correct_at_marks:
  !policy tops deploy_bc runtime_bc am tx ret es rpolicy unit out prog cp vs marks.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    o1_pipeline rpolicy unit = SOME out /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    gas_variant vs (entry_venom_state prog cp es) /\
    (!H. raw_unit_memory_ok unit.cu_context vs /\
         ptr_discipline 0 unit.cu_context vs /\
         taint_within (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
           unit.cu_context vs /\
         mem_inv dload_offset_ok unit.cu_context vs /\
         mem_inv dload_headroom_ok unit.cu_context vs ==>
         ctx_sim (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
           unit.cu_context out.po_unit.cu_context vs (entry_venom_state prog cp es) /\
         o1_lowered_inv out.po_unit.cu_context (entry_venom_state prog cp es)) /\
    source_unit_execution_correct_at marks tops ret am tx unit vs
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       !tail.
         source_storage_ok am tx (MAP SND (call_trace es))
           (gas_explicit marks vs.vs_gas_readings ++ tail) /\
         call_outcomes_storage_ok am tx (MAP SND (call_trace es))
           (gas_explicit marks vs.vs_gas_readings ++ tail) ==>
         call_result_rel_at (gas_explicit marks vs.vs_gas_readings ++ tail)
           tops ret am tx es r es')
Proof
  cheat
QED

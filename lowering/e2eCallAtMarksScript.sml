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

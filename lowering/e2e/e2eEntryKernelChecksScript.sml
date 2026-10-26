(* Compiler entry producer contracts. *)
Theory e2eEntryKernelChecks
Ancestors
  e2eProducers

val _ = Parse.hide "cp";

(* Exact four-contract consumer, not a theorem-name-only receipt. *)
Theorem entry_producers_exact_schema:
  (!rpolicy unit out cp Inv.
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    unit_shape_ok out.po_unit /\
    codegen_memory_obligations Inv out.po_unit.cu_context cp ==>
    codegen_context_obligations Inv out.po_unit.cu_context cp) /\
  (!tops prog am tx es cp.
    call_state_rel tops (assemble prog) am tx es ==>
    initial_venom_state_rel am tx (entry_venom_state prog cp es)) /\
  (!prog cp es. o1_initial_state_ok (entry_venom_state prog cp es)) /\
  (!tops prog am tx es u cp.
    call_state_rel tops (assemble prog) am tx es /\ unit_shape_ok u ==>
    initial_ctx_rel cp prog u.cu_context (entry_venom_state prog cp es) es)
Proof
  rpt conj_tac >|
    [ACCEPT_TAC o1_pipeline_codegen_obligations,
     ACCEPT_TAC entry_venom_state_initial_venom_state_rel,
     ACCEPT_TAC entry_venom_state_o1_initial_state_ok,
     ACCEPT_TAC entry_venom_state_initial_ctx_rel]
QED

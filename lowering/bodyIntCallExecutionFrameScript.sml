(* Successful counted witnesses retain their caller's label environment.
   The path theorem includes INVOKE (and restores the caller's labels). *)
Theory bodyIntCallExecutionFrame
Ancestors
  bodyIntCallProducerInterface stmtSimAugAssignPlaceMemory gasSummary
  gasOutcome fragGasMode venomState

Theorem intcall_marked_exec_labels:
  gas_marked_exec memory (ctx,func) source (es,s) marks res ee (OK t) ==>
  t.vs_labels = s.vs_labels
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  drule aug_place_marked_path_labels >> simp[]
QED

Theorem intcall_outcome_labels:
  gas_outcome memory tops (ctx,func) source (es,s) Q R ==>
  gas_outcome memory tops (ctx,func) source (es,s)
    (\res ee t. Q res ee t /\ t.vs_labels = s.vs_labels) R
Proof
  strip_tac >> drule gas_outcome_strengthen_witness >>
  disch_then (qspec_then `\res ee t. t.vs_labels = s.vs_labels` mp_tac) >>
  simp[] >> impl_tac >- (rpt strip_tac >> gvs[] >>
    drule intcall_marked_exec_labels >> simp[]) >> simp[]
QED

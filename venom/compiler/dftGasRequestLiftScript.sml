(* Join the request-aware fuel simulation with the directional swap proof.
   The fixed universal swap premise is discharged here, not exported to
   consumers of the context simulation. *)
Theory dftGasRequestLift
Ancestors
  dftGasRequestFuel dftGasRequestSwap

Theorem dft_ev_context_sim_rq:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ o1_ctx_shape C /\ dead_wf D /\
  ctx_labels_bound C s.vs_labels /\ o1_run_state_ok s /\
  terminates (ev_context orc fuel C s) ==>
  dft_rq_res_rel D (ev_context orc fuel C s) (ev_context orc fuel C' s)
Proof
  strip_tac >> irule dft_ev_context_sim_rq_conditional >> simp[] >>
  rpt strip_tac >> irule ev_suffix_swap_rq >> simp[]
QED

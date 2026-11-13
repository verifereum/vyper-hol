(*
 * DFT's request companion, under the input oracle dft_ctx_sim_gas chooses:
 * the same chosen input state gives the simulation, the abort companion
 * (ctx_abort_rq) and the lowered invariant.  DFT may run an ASSERT before
 * a CALL it does not depend on, so the output's requests at an abort are
 * a prefix of the input's, not the whole list.
 *)
Theory dftRequestsGas
Ancestors
  dftGasRequestContract dftGasRequestLift dftGasRequestSwap dftGasRequestPartner
  dftGasRequestSchedule dftGasRequestRel
  dftContractGas o1RequestContract o1PassContract o1PassLift unitMemInv
  dftDefs venomExecSemantics venomState list

Theorem dft_ctx_sim_rq_gas:
  LIST_REL (\fn fn'. fn' = dft_fn fn) C.ctx_functions C'.ctx_functions /\
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  C'.ctx_entry = C.ctx_entry /\ C'.ctx_global_reserved = C.ctx_global_reserved /\
  o1_ctx_shape C /\ dead_wf D /\
  ctx_labels_bound C vs'.vs_labels /\ o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\
       ctx_abort_rq D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
Proof
  strip_tac >>
  irule dft_ctx_sim_rq_gas_conditional >>
  simp[] >> rpt strip_tac >>
  irule dft_ev_context_sim_rq >> simp[]
QED

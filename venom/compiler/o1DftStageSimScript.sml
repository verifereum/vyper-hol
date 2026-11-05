(*
 * DFT's stage simulation in the gas form (piece of o1ContractDft).
 *
 * DFT may move a GAS read past another GAS read or an INVOKE, so C'
 * consumes the gas readings in another order than C.  For the run of C'
 * from vs', the witness vs is vs' with the readings C' consumes put back
 * in the order C reads them; every terminating run of C from vs is then
 * matched by a run of C' from vs', and the memory invariant carries over.
 *)
Theory o1DftStageSim
Ancestors
  o1PassContract venomPassSchedule venomWf

Theorem dft_stage_sim_gas:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  dead_wf D /\ o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
Proof
  cheat
QED

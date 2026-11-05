(*
 * DFT keeps wf_ssa (piece of o1ContractDft): each of its blocks is a
 * dependency-respecting schedule of the original block, so every use
 * still follows its definition.
 *)
Theory o1DftStageSsa
Ancestors
  o1PassContract venomPassSchedule venomWf

Theorem dft_stage_wf_ssa:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions ==>
  EVERY wf_ssa C'.ctx_functions
Proof
  cheat
QED

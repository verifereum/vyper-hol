(*
 * DFT's stage simulation at run 7 in the gas form, from the
 * context-level simulation over its function relation (dft_ctx_sim_gas)
 * and the labels code_layout_valid binds (dft_ctx_labels_bound).
 *)
Theory o1DftStageSim
Ancestors
  o1DftStageSsa dftContractGas o1PassContract venomPassSchedule venomWf

Theorem dft_stage_sim_gas:
  ctx_pass_stage rpolicy (CFP_Simple VP_DFT) view C C' /\ o1_pre 7 C C' /\
  dead_wf D /\ o1_ctx_shape C /\ EVERY wf_ssa C.ctx_functions /\
  o1_run_state_ok vs' ==>
  ?vs. gas_variant vs vs' /\ ctx_sim D C C' vs vs' /\
       (o1_lowered_inv C vs ==> o1_lowered_inv C' vs')
Proof
  strip_tac >> drule_all dft_stage_fn_rel >> strip_tac >>
  drule ctx_pass_stage_dft >> strip_tac >>
  irule dft_ctx_sim_gas >> simp[] >>
  irule dft_ctx_labels_bound >> gvs[o1_run_state_ok_def]
QED

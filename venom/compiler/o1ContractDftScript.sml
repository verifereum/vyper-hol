(*
 * DFT (stage 7) against the O1 pass contract, in the gas form: the
 * admission o1ContractTheorems re-exports, proved from its pieces.
 *
 * Row 7 (o1_ssa_inv) gives DFT wf_ssa.  When the input is not SSA the
 * row fails and any gas variant does; otherwise the stage simulation
 * supplies the witness, and row 8 is its memory invariant plus DFT
 * keeping wf_ssa.
 *)
Theory o1ContractDft
Ancestors
  o1DftStepAt o1DftStageSim o1DftStageSsa
  dftContractGas o1PassContract venomPassSchedule venomCompilerTypes

Theorem dft_stage_walk_gas:
  o1_run_contract_gas rpolicy D 7
Proof
  simp[o1_run_contract_gas_def, o1_fn_passes_def, o1_stage_contract_gas_def,
       o1_inv_def, o1_ssa_inv_def] >>
  rpt strip_tac >>
  Cases_on `EVERY wf_ssa C.ctx_functions`
  >- (drule_all dft_stage_sim_gas >> strip_tac >>
      qexists_tac `vs` >>
      `gas_variant vs vs'` by metis_tac[dft_gas_replay_variant] >> rw[] >> irule dft_stage_wf_ssa >> metis_tac[]) >>
  qexists_tac `vs'` >> simp[gas_variant_refl]
QED

Theorem o1_contract_dft:
  o1_step_contract_at 7 rpolicy (CFP_Simple VP_DFT) /\
  o1_run_contract_gas rpolicy D 7
Proof
  simp[dft_step_contract_at, dft_stage_walk_gas]
QED

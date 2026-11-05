(*
 * DFT (stage 7) against the O1 pass contract: the admission
 * o1ContractTheorems re-exports.
 *)
Theory o1ContractDft
Ancestors
  o1PassContract venomPassSchedule venomCompilerTypes

(* DFT reorders GAS reads: forall-out exists-in over the oracle. *)
Theorem o1_contract_dft:
  o1_step_contract_at 7 rpolicy (CFP_Simple VP_DFT) /\
  o1_run_contract_gas rpolicy D 7
Proof
  cheat
QED

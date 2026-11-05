(*
 * MakeSSA, which runs twice (stages 0 and 4), against the O1 pass
 * contract: the admissions o1ContractTheorems re-exports.
 *)
Theory o1ContractMakeSsa
Ancestors
  o1PassContract venomPassSchedule venomCompilerTypes

Theorem o1_contract_make_ssa_1:
  o1_step_contract_at 0 rpolicy (CFP_Simple VP_MakeSSA) /\
  o1_run_contract rpolicy D 0
Proof
  cheat
QED

Theorem o1_contract_make_ssa_2:
  o1_step_contract_at 4 rpolicy (CFP_Simple VP_MakeSSA) /\
  o1_run_contract rpolicy D 4
Proof
  cheat
QED

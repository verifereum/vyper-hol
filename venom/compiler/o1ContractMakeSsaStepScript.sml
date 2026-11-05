(*
 * MakeSSA's step contract, for both of its O1 runs: the output keeps the
 * O1 function shape, its fresh names and instruction ids come from the
 * supply, it maps no labels, the supply stays ok, and it adds no ALLOCA
 * (the only function row).
 *)
Theory o1ContractMakeSsaStep
Ancestors
  o1PassContract makeSsaCurrentDefs venomPassSchedule irSupply

Theorem make_ssa_step_contract_at:
  o1_step_contract_at k rpolicy (CFP_Simple VP_MakeSSA)
Proof
  cheat
QED

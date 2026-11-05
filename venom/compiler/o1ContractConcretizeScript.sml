(*
 * ConcretizeMemLoc (stage 2) against the O1 pass contract: the admission
 * o1ContractTheorems re-exports.
 *)
Theory o1ContractConcretize
Ancestors
  o1PassContract venomPassSchedule venomCompilerTypes

(* ConcretizeMemLoc reads callee layouts (the walk view): the raw
   invariant becomes the static one. *)
Theorem o1_contract_concretize_mem_loc:
  o1_step_contract_at 2 rpolicy (CFP_Simple VP_ConcretizeMemLoc) /\
  o1_run_contract rpolicy D 2
Proof
  cheat
QED

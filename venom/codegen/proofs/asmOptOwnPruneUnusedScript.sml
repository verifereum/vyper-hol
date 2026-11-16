(* First client of the shared own-code splice simulation. *)
Theory asmOptOwnPruneUnused
Ancestors
  asmSpliceOwn asmSymPcOwn finalizerContractOwn
  asmSplice asmSymPc asmSymOwnCode asmSymSem asmOptimizer asmWf asmSem

Theorem prune_unused_jumpdests_refines_own:
  ∀p. asm_refines_own p (FST (prune_unused_jumpdests p))
Proof
  cheat
QED

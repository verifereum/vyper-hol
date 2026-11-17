(* Discharge the own-code finalizer contract with all seven rule proofs. *)
Theory asmOptFinalizerOwn
Ancestors
  asmSymOwnCode finalizerContractOwn asmOptOwnPruneUnreachable
  asmOptOwnMergeIszero asmOptOwnMergeJumpdests asmOptOwnPruneJumps
  asmOptOwnInefficientJumps asmOptOwnPruneUnused asmOptOwnPeephole

val rule_obligations = LIST_CONJ
  [prune_unreachable_code_refines_own, merge_iszero_refines_own,
   merge_jumpdests_refines_own, prune_inefficient_jumps_refines_own,
   optimize_inefficient_jumps_refines_own, prune_unused_jumpdests_refines_own,
   stack_peephole_opts_refines_own];

Theorem asm_opt_finalizer_refines_own:
  asm_opt_finalizer rp p = SOME p' ⇒ asm_refines_own p p'
Proof
  MATCH_ACCEPT_TAC
    (REWRITE_RULE [finalizer_correct_own_def]
      (MATCH_MP asm_opt_finalizer_correct_own rule_obligations))
QED

Theorem accepted_finalizers_correct_own_thm =
  MATCH_MP accepted_finalizers_correct_own rule_obligations

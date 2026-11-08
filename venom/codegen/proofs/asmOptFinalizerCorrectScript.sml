(*
 * The asm optimizer meets the finalizer contract, with no hypotheses.
 *
 * finalizerContract proves both results from the seven rule obligations;
 * each rule theory proves one of them.
 *
 * TOP-LEVEL:
 *   asm_opt_finalizer_meets_contract  — finalizer_correct asm_opt_finalizer
 *   accepted_finalizers_meet_contract — every accepted finalizer is correct
 *)

Theory asmOptFinalizerCorrect
Ancestors
  finalizerContract asmOptPruneUnreachable asmOptMergeIszero
  asmOptMergeJumpdests asmOptPruneJumps asmOptInefficientJumps
  asmOptPruneUnused asmOptPeephole

val rule_obligations = LIST_CONJ
  [prune_unreachable_code_refines, merge_iszero_refines,
   merge_jumpdests_refines, prune_inefficient_jumps_refines,
   optimize_inefficient_jumps_refines, prune_unused_jumpdests_refines,
   stack_peephole_opts_refines];

Theorem asm_opt_finalizer_meets_contract =
  MATCH_MP asm_opt_finalizer_correct rule_obligations

Theorem accepted_finalizers_meet_contract =
  MATCH_MP accepted_finalizers_correct rule_obligations

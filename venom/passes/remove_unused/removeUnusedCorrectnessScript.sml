(*
 * Remove Unused Variables — Correctness (API)
 *
 * Top-level theorems only. All proofs in proofs/removeUnusedCorrectnessProofs.
 *)

Theory removeUnusedCorrectness
Ancestors
  removeUnusedCorrectnessProofs

Theorem remove_unused_function_correct =
  removeUnusedCorrectnessProofsTheory.remove_unused_function_correct

Theorem remove_unused_pass_correct =
  removeUnusedCorrectnessProofsTheory.remove_unused_pass_correct

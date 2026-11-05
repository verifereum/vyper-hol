(*
 * Remove Unused Variables — Correctness (API)
 *
 * Top-level theorems only. All proofs in proofs/removeUnusedCorrectnessProofs.
 *)

Theory removeUnusedCorrectness
Ancestors
  removeUnusedCorrectnessProofs

Theorem remove_unused_function_correct_gas =
  removeUnusedCorrectnessProofsTheory.remove_unused_function_correct_gas

Theorem remove_unused_pass_correct_gas =
  removeUnusedCorrectnessProofsTheory.remove_unused_pass_correct_gas

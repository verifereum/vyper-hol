(*
 * Memmerging — Correctness (API)
 *
 * Re-exports from proofs/mmCorrectnessProofs.
 * Definitions and local lemmas are in mmCorrectnessProofs.
 *)

Theory mmCorrectness
Ancestors
  mmCorrectnessProofs

Theorem transform_block_label =
  mmCorrectnessProofsTheory.transform_block_label

Theorem transform_function_eq =
  mmCorrectnessProofsTheory.transform_function_eq

Theorem flat_map_same_start_block_bridge =
  mmCorrectnessProofsTheory.flat_map_same_start_block_bridge

Theorem mm_block_simulates_memzero =
  mmCorrectnessProofsTheory.mm_block_simulates_memzero

Theorem mode_run_insts_lift_result =
  mmCorrectnessProofsTheory.mode_run_insts_lift_result

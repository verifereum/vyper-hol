(*
 * Memmerging — Block / Function / Pass Simulation (API)
 *
 * TOP-LEVEL:
 *   mm_block_simulates   — block-level simulation
 *   mm_function_correct  — function-level simulation
 *   mm_pass_correct      — pass correctness
 *)

Theory mmBlockSim
Ancestors
  mmBlockSimProofs

Theorem mm_block_simulates_dload =
  mmBlockSimProofsTheory.mm_block_simulates_dload

Theorem mm_block_simulates =
  mmBlockSimProofsTheory.mm_block_simulates

Theorem mm_function_correct =
  mmBlockSimProofsTheory.mm_function_correct

Theorem mm_pass_correct =
  mmBlockSimProofsTheory.mm_pass_correct

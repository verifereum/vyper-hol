(*
 * Alloca Remapping Properties (API)
 *
 * Exported theorems for alloca remap preservation. Proof internals
 * are in allocaRemapProofsTheory.
 *
 * TOP-LEVEL:
 *   step_inst_base_preserves_remap — per-instruction remap preservation
 *   exec_alloca_preserves_remap    — ALLOCA extends remap relation
 *   run_block_preserves_remap      — block-level preservation (main theorem)
 *)

Theory allocaRemapProps
Ancestors
  allocaRemapProofs

Theorem step_inst_base_preserves_remap =
  allocaRemapProofsTheory.step_inst_base_preserves_remap

Theorem exec_alloca_preserves_remap =
  allocaRemapProofsTheory.exec_alloca_preserves_remap

Theorem run_block_preserves_remap =
  allocaRemapProofsTheory.run_block_preserves_remap

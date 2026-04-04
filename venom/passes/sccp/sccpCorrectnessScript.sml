(*
 * SCCP — Correctness (API)
 *
 * Pure re-exports from proofs/sccpCorrectnessProofs.
 *)

Theory sccpCorrectness
Ancestors
  sccpCorrectnessProofs

Theorem sccp_pass_correct_fn =
  sccpCorrectnessProofsTheory.sccp_pass_correct_fn

Theorem sccp_pass_correct =
  sccpCorrectnessProofsTheory.sccp_pass_correct

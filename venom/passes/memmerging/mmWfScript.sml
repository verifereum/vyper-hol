(*
 * Memmerging — Well-formedness Preservation (API)
 *
 * TOP-LEVEL (over transform_function_supply):
 *   mm_preserves_wf_function   — wf_function preserved
 *   mm_preserves_ssa_form      — ssa_form preserved
 *)

Theory mmWf
Ancestors
  mmSupplyWfProofs mmSupplySsaProofs

Theorem mm_preserves_wf_function =
  mmSupplyWfProofsTheory.mm_preserves_wf_function

Theorem mm_preserves_ssa_form =
  mmSupplySsaProofsTheory.mm_preserves_ssa_form

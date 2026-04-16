(*
 * Memmerging — Well-formedness Preservation (API)
 *
 * TOP-LEVEL:
 *   mm_preserves_wf_function   — wf_function preserved
 *   mm_preserves_ssa_form      — ssa_form preserved (CHEATED, needs mm_fresh_names_ok + fn_inst_ids_distinct)
 *)

Theory mmWf
Ancestors
  mmWfProofs

Theorem mm_preserves_wf_function =
  mmWfProofsTheory.mm_preserves_wf_function

Theorem mm_preserves_ssa_form =
  mmWfProofsTheory.mm_preserves_ssa_form

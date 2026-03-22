(*
 * Stack Order Analysis — Consumer-Facing Properties
 *
 * from_to_wf preservation is FALSE even with single_use_form.
 * See proofs/stackOrderCexScript.sml (Counterexample 2) for mechanical proof.
 *)

Theory stackOrderProps
Ancestors
  stackOrderProofs cfgAnalysisProps

Theorem so_analyze_block_needed_distinct:
  ∀cfg lr from_to lbl insts needed stack.
    (needed, stack) = so_analyze_block cfg lr from_to lbl insts ⇒
    ALL_DISTINCT needed
Proof
  ACCEPT_TAC so_analyze_block_needed_distinct_proof
QED

Theorem so_get_stack_sound:
  ∀fn cfg lr from_to lbl merged from_to'.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    (merged, from_to') = so_get_stack cfg lr fn from_to lbl ⇒
    ALL_DISTINCT merged
Proof
  ACCEPT_TAC so_get_stack_sound_proof
QED

Theorem so_merge_prefix:
  ∀orders n. MEM n orders ⇒
    isPREFIX (so_merge orders) n
Proof
  ACCEPT_TAC so_merge_prefix_proof
QED

Theorem so_from_to_includes_live:
  ∀lr fn from_to origin succ v succ_bb.
    lookup_block succ fn.fn_blocks = SOME succ_bb ∧
    MEM v (input_vars_from origin succ_bb.bb_instructions
             (live_vars_at lr succ 0)) ⇒
    MEM v (so_from_to_query lr fn from_to origin succ)
Proof
  ACCEPT_TAC so_from_to_includes_live_proof
QED

Theorem so_from_to_includes_base:
  ∀lr fn from_to origin succ v needed.
    FLOOKUP from_to (origin, succ) = SOME needed ∧
    MEM v needed ⇒
    MEM v (so_from_to_query lr fn from_to origin succ)
Proof
  ACCEPT_TAC so_from_to_includes_base_proof
QED



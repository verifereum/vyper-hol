(*
 * Stack Order Analysis — Consumer-Facing Properties
 *
 * API for the DFT (code generation) pass.
 * Proved in proofs/stackOrderProofsScript.sml, imported via ACCEPT_TAC.
 *
 *   so_get_stack_sound      — from_to invariant preserved, merged is distinct
 *   so_merge_prefix         — merge result is prefix of each input
 *   so_from_to_includes_live — from_to query includes liveness input vars
 *   so_from_to_includes_base — from_to query includes base map entries
 *)

Theory stackOrderProps
Ancestors
  stackOrderProofs

Theorem so_get_stack_sound:
  ∀fn cfg lr from_to lbl merged from_to'.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    lr = liveness_analyze fn ∧
    from_to_wf lr from_to ∧
    (merged, from_to') = so_get_stack cfg lr fn from_to lbl ⇒
    ALL_DISTINCT merged ∧
    from_to_wf lr from_to'
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

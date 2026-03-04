(*
 * Stack Order Analysis — Proofs
 *
 * Internal lemmas and proofs of consumer-facing properties.
 * All cheated — to be filled in.
 *
 * Internal lemmas:
 *   so_handle_inst_stack_top_proof  — operands on top after handle_inst
 *   so_analyze_block_needed_distinct_proof — needed list has no duplicates
 *   so_needed_are_live_proof        — needed vars are live at block entry
 *
 * API proofs (consumed by stackOrderProps via ACCEPT_TAC):
 *   so_get_stack_sound_proof
 *   so_merge_prefix_proof
 *   so_from_to_includes_live_proof
 *   so_from_to_includes_base_proof
 *)

Theory stackOrderProofs
Ancestors
  stackOrderDefs

(* ==========================================================================
   Internal lemmas
   ========================================================================== *)

(* After handle_inst, the top n elements of the stack equal the instruction's
   operands in order. Counterpart of the assertion in Python's analyze_bb.
   Requires distinct operands (duplicates need DUP). *)
Theorem so_handle_inst_stack_top_proof:
  ∀stack needed inst stack' needed'.
    ALL_DISTINCT inst.inst_operands ∧
    (stack', needed') = so_handle_inst (stack, needed) inst ⇒
    let n = LENGTH inst.inst_operands in
    n ≤ LENGTH stack' ∧
    DROP (LENGTH stack' - n) stack' = inst.inst_operands
Proof
  cheat
QED

(* The needed list produced by analyze_block has no duplicates. *)
Theorem so_analyze_block_needed_distinct_proof:
  ∀cfg lr from_to lbl insts needed stack.
    (needed, stack) = so_analyze_block cfg lr from_to lbl insts ⇒
    ALL_DISTINCT needed
Proof
  cheat
QED

(* Every variable in the needed list is live at block entry. *)
Theorem so_needed_are_live_proof:
  ∀fn cfg lr from_to lbl bb needed stack v.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    lr = liveness_analyze fn ∧
    from_to_wf lr from_to ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    bb.bb_label = lbl ∧
    (needed, stack) =
      so_analyze_block cfg lr from_to lbl bb.bb_instructions ∧
    MEM v needed ⇒
    MEM v (live_vars_at lr lbl 0)
Proof
  cheat
QED

(* ==========================================================================
   API proofs (consumed by stackOrderProps via ACCEPT_TAC)
   ========================================================================== *)

Theorem so_get_stack_sound_proof:
  ∀fn cfg lr from_to lbl merged from_to'.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    lr = liveness_analyze fn ∧
    from_to_wf lr from_to ∧
    (merged, from_to') = so_get_stack cfg lr fn from_to lbl ⇒
    ALL_DISTINCT merged ∧
    from_to_wf lr from_to'
Proof
  cheat
QED

Theorem so_merge_prefix_proof:
  ∀orders n. MEM n orders ⇒
    isPREFIX (so_merge orders) n
Proof
  cheat
QED

Theorem so_from_to_includes_live_proof:
  ∀lr fn from_to origin succ v succ_bb.
    lookup_block succ fn.fn_blocks = SOME succ_bb ∧
    MEM v (input_vars_from origin succ_bb.bb_instructions
             (live_vars_at lr succ 0)) ⇒
    MEM v (so_from_to_query lr fn from_to origin succ)
Proof
  cheat
QED

Theorem so_from_to_includes_base_proof:
  ∀lr fn from_to origin succ v needed.
    FLOOKUP from_to (origin, succ) = SOME needed ∧
    MEM v needed ⇒
    MEM v (so_from_to_query lr fn from_to origin succ)
Proof
  cheat
QED

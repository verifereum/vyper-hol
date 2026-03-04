(*
 * Stack Order Analysis — Safety Properties
 *
 * Consumer-facing correctness properties for stack_order analysis.
 * All cheated — proofs deferred to proofs/ subdirectory.
 *
 *   so_get_stack_sound              — main DFT entry: preserves from_to invariant,
 *                                     merged needed is distinct
 *   so_needed_are_live              — needed vars are live at block entry
 *   so_analyze_block_needed_distinct — needed list has no duplicates
 *   so_handle_inst_stack_top        — after handle_inst, operands are on top
 *   so_merge_prefix                 — merge result is prefix of each input
 *   so_from_to_includes_live        — from_to query includes liveness input vars
 *   so_from_to_includes_base        — from_to query includes base map entries
 *)

Theory stackOrderProps
Ancestors
  stackOrderDefs

(* ==========================================================================
   Top-level: so_get_stack soundness for DFT consumer
   ========================================================================== *)

(* The from_to well-formedness invariant: every variable stored in the
   from_to map is live at the entry of the target block. *)
Definition from_to_wf_def:
  from_to_wf lr from_to ⇔
    ∀pred succ ns w.
      FLOOKUP from_to (pred, succ) = SOME ns ∧ MEM w ns ⇒
      MEM w (live_vars_at lr succ 0)
End

(* Main soundness theorem for the DFT consumer. The DFT calls so_get_stack
   per block, threading from_to. This theorem says:
   (1) the merged needed list has no duplicates (placeable at distinct
       stack positions), and
   (2) the updated from_to map preserves the well-formedness invariant
       (safe to pass to the next so_get_stack call).
   Together with so_merge_prefix (merged is prefix of each successor's
   needed) and so_from_to_includes_live/base (edge queries are complete),
   this gives the DFT proof everything it needs inductively. *)
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
  cheat
QED

(* ==========================================================================
   Component properties
   ========================================================================== *)

(* Merged needed list is a prefix of every individual successor's needed list.
   Ensures the common ordering is compatible with all successors. *)
Theorem so_merge_prefix:
  ∀orders n. MEM n orders ⇒
    isPREFIX (so_merge orders) n
Proof
  cheat
QED

(* After handle_inst, the top n elements of the stack equal the instruction's
   operands in order. This is the HOL4 counterpart of the assertion in
   Python's analyze_bb loop. Requires distinct operands (duplicates need DUP). *)
Theorem so_handle_inst_stack_top:
  ∀stack needed inst stack' needed'.
    ALL_DISTINCT inst.inst_operands ∧
    (stack', needed') = so_handle_inst (stack, needed) inst ⇒
    let n = LENGTH inst.inst_operands in
    n ≤ LENGTH stack' ∧
    DROP (LENGTH stack' - n) stack' = inst.inst_operands
Proof
  cheat
QED

(* The needed list produced by analyze_block has no duplicates.
   Follows from so_add_needed preserving ALL_DISTINCT at each step. *)
Theorem so_analyze_block_needed_distinct:
  ∀cfg lr from_to lbl insts needed stack.
    (needed, stack) = so_analyze_block cfg lr from_to lbl insts ⇒
    ALL_DISTINCT needed
Proof
  cheat
QED

(* Every variable in the needed list is live at block entry.
   The from_to precondition is needed because the terminator handler
   pulls variables from the from_to map (populated by analyzing successors). *)
Theorem so_needed_are_live:
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

(* The from_to query includes every variable from PHI-aware liveness
   at the edge (origin → succ). *)
Theorem so_from_to_includes_live:
  ∀lr fn from_to origin succ v succ_bb.
    lookup_block succ fn.fn_blocks = SOME succ_bb ∧
    MEM v (input_vars_from origin succ_bb.bb_instructions
             (live_vars_at lr succ 0)) ⇒
    MEM v (so_from_to_query lr fn from_to origin succ)
Proof
  cheat
QED

(* The from_to query includes every variable from the base from_to map. *)
Theorem so_from_to_includes_base:
  ∀lr fn from_to origin succ v needed.
    FLOOKUP from_to (origin, succ) = SOME needed ∧
    MEM v needed ⇒
    MEM v (so_from_to_query lr fn from_to origin succ)
Proof
  cheat
QED

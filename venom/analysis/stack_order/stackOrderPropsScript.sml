(*
 * Stack Order Analysis — Safety Properties
 *
 * Theorem statements for stack_order correctness.
 * All cheated — proofs deferred.
 *
 * TOP-LEVEL:
 *   so_needed_are_live        — needed vars are live at block entry
 *   so_needed_distinct        — needed list has no duplicates
 *   so_handle_inst_stack_top  — after handle_inst, operands are on top
 *   so_from_to_includes_live  — from_to query includes liveness input vars
 *
 * Helper (stack/merge properties):
 *   max_same_prefix_is_prefix — result is prefix of both inputs
 *   so_merge_prefix           — merge result is prefix of each input
 *   so_add_needed_mem         — added variable is a member
 *   so_add_needed_preserves   — existing members are preserved
 *   so_add_needed_distinct    — preserves ALL_DISTINCT
 *   so_reorder_length         — reorder preserves stack length
 *   stack_swap_length         — swap preserves stack length
 *   stack_swap_to_length      — swap_to preserves stack length
 *)

Theory stackOrderProps
Ancestors
  stackOrderDefs

(* ==========================================================================
   Stack operation properties
   ========================================================================== *)

Theorem stack_find_some:
  ∀op stack i.
    stack_find op stack = SOME i ⇒
    i < LENGTH stack ∧ EL i stack = op
Proof
  cheat
QED

Theorem stack_find_none:
  ∀op stack.
    stack_find op stack = NONE ⇔ ¬MEM op stack
Proof
  cheat
QED

Theorem stack_swap_length:
  ∀stack op. LENGTH (stack_swap stack op) = LENGTH stack
Proof
  cheat
QED

Theorem stack_swap_mem:
  ∀stack op x. MEM x (stack_swap stack op) ⇔ MEM x stack
Proof
  cheat
QED

Theorem stack_swap_to_length:
  ∀stack depth. LENGTH (stack_swap_to stack depth) = LENGTH stack
Proof
  cheat
QED

Theorem stack_swap_to_mem:
  ∀stack depth x. MEM x (stack_swap_to stack depth) ⇔ MEM x stack
Proof
  cheat
QED

(* ==========================================================================
   Merge / prefix properties
   ========================================================================== *)

Theorem max_same_prefix_is_prefix:
  ∀a b. isPREFIX (max_same_prefix a b) a ∧
         isPREFIX (max_same_prefix a b) b
Proof
  cheat
QED

Theorem max_same_prefix_length:
  ∀a b. LENGTH (max_same_prefix a b) ≤ LENGTH a ∧
         LENGTH (max_same_prefix a b) ≤ LENGTH b
Proof
  cheat
QED

Theorem max_same_prefix_comm:
  ∀a b. max_same_prefix a b = max_same_prefix b a
Proof
  cheat
QED

Theorem so_merge_prefix:
  ∀orders n. MEM n orders ⇒
    isPREFIX (so_merge orders) n
Proof
  cheat
QED

(* ==========================================================================
   Needed list properties
   ========================================================================== *)

Theorem so_add_needed_mem:
  ∀needed v. MEM v (so_add_needed needed v)
Proof
  cheat
QED

Theorem so_add_needed_preserves:
  ∀needed u v. MEM u needed ⇒ MEM u (so_add_needed needed v)
Proof
  cheat
QED

Theorem so_add_needed_distinct:
  ∀needed v.
    ALL_DISTINCT needed ⇒ ALL_DISTINCT (so_add_needed needed v)
Proof
  cheat
QED

(* ==========================================================================
   Reorder properties
   ========================================================================== *)

Theorem so_reorder_length:
  ∀stack target. LENGTH (so_reorder stack target) = LENGTH stack
Proof
  cheat
QED

(* After reorder, target operands appear at top of stack in order.
   Precondition: all target operands are already on the stack. *)
Theorem so_reorder_correct:
  ∀stack target.
    (∀op. MEM op target ⇒ MEM op stack) ∧
    LENGTH target ≤ LENGTH stack ⇒
    DROP (LENGTH (so_reorder stack target) - LENGTH target)
         (so_reorder stack target) = target
Proof
  cheat
QED

(* ==========================================================================
   Instruction handler properties
   ========================================================================== *)

(* After handle_inst, the top of stack matches the instruction's operands.
   This corresponds to the assertion in Python's analyze_bb. *)
Theorem so_handle_inst_stack_top:
  ∀stack needed inst stack' needed'.
    (stack', needed') = so_handle_inst (stack, needed) inst ⇒
    let n = LENGTH inst.inst_operands in
    n ≤ LENGTH stack' ∧
    DROP (LENGTH stack' - n) stack' = inst.inst_operands
Proof
  cheat
QED

(* handle_inst preserves ALL_DISTINCT on needed *)
Theorem so_handle_inst_needed_distinct:
  ∀stack needed inst stack' needed'.
    ALL_DISTINCT needed ∧
    (stack', needed') = so_handle_inst (stack, needed) inst ⇒
    ALL_DISTINCT needed'
Proof
  cheat
QED

(* handle_assign preserves ALL_DISTINCT on needed *)
Theorem so_handle_assign_needed_distinct:
  ∀lr lbl idx stack needed inst stack' needed'.
    ALL_DISTINCT needed ∧
    (stack', needed') =
      so_handle_assign lr lbl idx (stack, needed) inst ⇒
    ALL_DISTINCT needed'
Proof
  cheat
QED

(* handle_terminator preserves ALL_DISTINCT on needed *)
Theorem so_handle_terminator_needed_distinct:
  ∀cfg from_to lbl stack needed inst stack' needed'.
    ALL_DISTINCT needed ∧
    (stack', needed') =
      so_handle_terminator cfg from_to lbl (stack, needed) inst ⇒
    ALL_DISTINCT needed'
Proof
  cheat
QED

(* ==========================================================================
   Block analysis properties
   ========================================================================== *)

(* Needed list from analyze_block has no duplicates *)
Theorem so_analyze_block_needed_distinct:
  ∀cfg lr from_to lbl insts needed stack.
    (needed, stack) = so_analyze_block cfg lr from_to lbl insts ⇒
    ALL_DISTINCT needed
Proof
  cheat
QED

(* ==========================================================================
   Liveness connection
   ========================================================================== *)

(* Needed variables computed by analyze_block are live at block entry.
   Requires well-formed function and consistent liveness/cfg. *)
Theorem so_needed_are_live:
  ∀fn cfg lr from_to lbl bb needed stack v.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    lr = liveness_analyze fn ∧
    lookup_block lbl fn.fn_blocks = SOME bb ∧
    bb.bb_label = lbl ∧
    (needed, stack) =
      so_analyze_block cfg lr from_to lbl bb.bb_instructions ∧
    MEM v needed ⇒
    MEM v (live_vars_at lr lbl 0)
Proof
  cheat
QED

(* from_to query result includes all liveness input vars *)
Theorem so_from_to_includes_live:
  ∀lr fn from_to origin succ v succ_bb.
    lookup_block succ fn.fn_blocks = SOME succ_bb ∧
    MEM v (input_vars_from origin succ_bb.bb_instructions
             (live_vars_at lr succ 0)) ⇒
    MEM v (so_from_to_query lr fn from_to origin succ)
Proof
  cheat
QED

(* from_to query includes the base from_to entries *)
Theorem so_from_to_includes_base:
  ∀lr fn from_to origin succ v.
    FLOOKUP from_to (origin, succ) = SOME needed ∧
    MEM v needed ⇒
    MEM v (so_from_to_query lr fn from_to origin succ)
Proof
  cheat
QED

val _ = export_theory();

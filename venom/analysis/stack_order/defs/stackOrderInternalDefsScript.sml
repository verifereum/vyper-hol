(*
 * Stack Order Analysis — Internal Definitions
 *
 * Implementation details of the EVM stack simulation.
 * Not intended for direct use by consumers (DFT) — use the API in
 * stackOrderDefsScript.sml instead.
 *
 * Types:
 *   so_block_state       — per-block analysis state (stack, needed, idx)
 *
 * Stack operations:
 *   stack_find           — find index of first occurrence of operand
 *   stack_swap           — swap first occurrence of op to top
 *   stack_swap_to        — swap top to given depth
 *   so_reorder           — bring operands to top in target order
 *
 * Merge / needed:
 *   max_same_prefix      — longest common prefix of two lists
 *   so_merge             — merge multiple needed lists
 *   so_add_needed        — append var to needed (no duplicates)
 *
 * Instruction handlers:
 *   so_handle_inst       — general instruction handler (incl. PHI)
 *   so_handle_assign     — assign handler (uses next-inst liveness)
 *   so_handle_terminator — terminator handler (uses cfg, from_to map)
 *   so_step              — dispatch + operand pop/output push
 *
 * Block-level:
 *   so_analyze_block     — fold so_step over instructions
 *   so_record_from_to    — record needed for all predecessors
 *   so_analyze_succ      — analyze one successor, update from_to
 *)

Theory stackOrderInternalDefs
Ancestors
  list finite_map
  venomInst cfgDefs livenessDefs

(* ==========================================================================
   Types
   ========================================================================== *)

(* Per-block analysis state: simulated stack, needed variables, instruction index *)
Datatype:
  so_block_state = <|
    sobs_stack : operand list;
    sobs_needed : string list;
    sobs_idx : num
  |>
End

(* ==========================================================================
   Stack operations
   ========================================================================== *)

(* Find index of first occurrence of operand in stack.
   Python: reversed(enumerate(stack)) scan without break → finds first index. *)
Definition stack_find_def:
  stack_find op [] = NONE ∧
  stack_find op (x::xs) =
    if x = op then SOME (0:num)
    else OPTION_MAP SUC (stack_find op xs)
End

(* Swap first occurrence of op with top of stack.
   Python: _swap(stack, op) *)
Definition stack_swap_def:
  stack_swap stack op =
    case stack_find op stack of
      NONE => stack
    | SOME i =>
        let top = LENGTH stack - 1 in
        LUPDATE (EL i stack) top (LUPDATE (EL top stack) i stack)
End

(* Swap top of stack to given depth.
   Python: _swap_to(stack, depth)
   depth=0 → no-op, depth=1 → swap top with second-from-top, etc. *)
Definition stack_swap_to_def:
  stack_swap_to stack depth =
    let top = LENGTH stack - 1 in
    let idx = top - depth in
    LUPDATE (EL idx stack) top (LUPDATE (EL top stack) idx stack)
End

(* ==========================================================================
   Merge — longest common prefix
   ========================================================================== *)

(* Longest common prefix of two lists.
   Python: _max_same_prefix *)
Definition max_same_prefix_def:
  max_same_prefix [] _ = [] ∧
  max_same_prefix _ [] = [] ∧
  max_same_prefix (x::xs) (y::ys) =
    if x = y then x :: max_same_prefix xs ys else []
End

(* Merge multiple needed lists by common prefix.
   Python: _merge — FOLDL of max_same_prefix *)
Definition so_merge_def:
  so_merge [] = [] ∧
  so_merge (n::ns) = FOLDL max_same_prefix n ns
End

(* ==========================================================================
   Needed list management
   ========================================================================== *)

(* Add variable to needed list (preserving order, no duplicates).
   Python: _add_needed *)
Definition so_add_needed_def:
  so_add_needed needed v =
    if MEM v needed then needed else SNOC v needed
End

(* ==========================================================================
   Reorder — bring operands to top in target order
   ========================================================================== *)

(* Reorder: for each operand at index idx in target (count total),
   swap it to top, then swap_to at depth (count - idx - 1).
   Python: _reorder *)
Definition so_reorder_aux_def:
  so_reorder_aux stack count idx [] = stack ∧
  so_reorder_aux stack count idx (op::ops) =
    let s' = stack_swap stack op in
    let s'' = stack_swap_to s' (count - idx - 1) in
    so_reorder_aux s'' count (idx + 1) ops
End

Definition so_reorder_def:
  so_reorder stack target =
    so_reorder_aux stack (LENGTH target) 0 target
End

(* ==========================================================================
   Per-instruction handlers
   ========================================================================== *)

(* Handle general instruction (and PHI).
   For each operand: if variable and not on stack, add to needed.
   If not on stack, append. Then reorder to bring operands to top.
   Python: _handle_inst *)
Definition so_handle_inst_def:
  so_handle_inst (stack, needed) inst =
    let ops = inst.inst_operands in
    let (stack', needed') =
      FOLDL (λ(s, n) op.
        let n' = (case op of
                    Var v => if ¬MEM op s then so_add_needed n v else n
                  | _ => n) in
        let s' = if MEM op s then s else SNOC op s in
        (s', n'))
      (stack, needed) ops
    in
    (so_reorder stack' ops, needed')
End

(* Handle assign instruction.
   Checks next-instruction liveness to decide whether to dup or swap.
   Python: _handle_assign *)
Definition so_handle_assign_def:
  so_handle_assign lr lbl idx (stack, needed) inst =
    let src = HD inst.inst_operands in
    let next_live = live_vars_at lr lbl (idx + 1) in
    case src of
      Var v =>
        if MEM v next_live then
          (* src is live after assign: need it on stack, add to needed *)
          (SNOC src stack, so_add_needed needed v)
        else if ¬MEM src stack then
          (* src not live after and not on stack: push and add to needed *)
          (SNOC src stack, so_add_needed needed v)
        else
          (* src not live after but on stack: swap to top (reuse, effectively move) *)
          (stack_swap stack src, needed)
    | _ =>
        (* Non-variable source (literal/label): just push *)
        (SNOC src stack, needed)
End

(* Handle terminator instruction.
   Adds variable operands and merged successor needs to needed.
   Does NOT modify the stack (terminator is last instruction).
   Python: _handle_terminator *)
Definition so_handle_terminator_def:
  so_handle_terminator cfg from_to lbl (stack, needed) inst =
    let succs = cfg_succs_of cfg lbl in
    let orders = MAP (λsucc.
      case FLOOKUP from_to (lbl, succ) of
        NONE => []
      | SOME n => n) succs in
    (* Add variable operands not on stack to needed *)
    let needed' =
      FOLDL (λn op.
        case op of
          Var v => if ¬MEM op stack then so_add_needed n v else n
        | _ => n)
      needed inst.inst_operands
    in
    (* Add merged successor needs not on stack to needed *)
    let needed'' =
      FOLDL (λn v.
        if ¬MEM (Var v) stack then so_add_needed n v else n)
      needed' (so_merge orders)
    in
    (stack, needed'')
End

(* ==========================================================================
   Per-instruction step — dispatch + post-processing
   ========================================================================== *)

(* Process one instruction: dispatch to handler, pop operands, push outputs.
   Python: body of the for loop in analyze_bb *)
Definition so_step_def:
  so_step cfg lr from_to lbl st inst =
    let (stack', needed') =
      if inst.inst_opcode = ASSIGN then
        so_handle_assign lr lbl st.sobs_idx
          (st.sobs_stack, st.sobs_needed) inst
      else if is_terminator inst.inst_opcode then
        so_handle_terminator cfg from_to lbl
          (st.sobs_stack, st.sobs_needed) inst
      else (* PHI and normal instructions *)
        so_handle_inst (st.sobs_stack, st.sobs_needed) inst
    in
    (* Pop consumed operands, push outputs *)
    let n_ops = LENGTH inst.inst_operands in
    let stack'' = if n_ops = 0 then stack'
                  else TAKE (LENGTH stack' - n_ops) stack' in
    let stack''' = stack'' ++ MAP Var inst.inst_outputs in
    st with <| sobs_stack := stack''';
               sobs_needed := needed';
               sobs_idx := st.sobs_idx + 1 |>
End

(* ==========================================================================
   Block-level analysis
   ========================================================================== *)

(* Analyze a block: fold so_step over instructions, return (needed, stack).
   Python: analyze_bb (instruction processing part) *)
Definition so_analyze_block_def:
  so_analyze_block cfg lr from_to lbl insts =
    let init = <| sobs_stack := [];
                  sobs_needed := [];
                  sobs_idx := 0 |> in
    let final = FOLDL (so_step cfg lr from_to lbl) init insts in
    (final.sobs_needed, final.sobs_stack)
End

(* Record from_to entries: for each predecessor of lbl, map (pred, lbl) → needed.
   Python: tail of analyze_bb *)
Definition so_record_from_to_def:
  so_record_from_to cfg from_to lbl needed =
    FOLDL (λft pred. ft |+ ((pred, lbl), needed))
      from_to (cfg_preds_of cfg lbl)
End

(* Analyze a successor block and update from_to map.
   Python: analyze_bb called from get_stack *)
Definition so_analyze_succ_def:
  so_analyze_succ cfg lr fn from_to succ_lbl =
    case lookup_block succ_lbl fn.fn_blocks of
      NONE => from_to
    | SOME bb =>
        let (needed, _) =
          so_analyze_block cfg lr from_to succ_lbl bb.bb_instructions in
        so_record_from_to cfg from_to succ_lbl needed
End

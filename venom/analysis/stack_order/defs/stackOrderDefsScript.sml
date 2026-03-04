(*
 * Stack Order Analysis — Consumer API
 *
 * Ports vyper/venom/analysis/stack_order.py to HOL4.
 * EVM stack simulation: determines what order variables need to be
 * on the physical EVM stack when entering each basic block.
 * Used by the DFT (Depth-First Traversal) code generation pass.
 *
 *   so_get_stack        — analyze successors of a block, return merged needed
 *   so_from_to_query    — query needed vars for a specific edge (with liveness)
 *   from_to_wf          — well-formedness invariant for from_to map
 *
 * Internal definitions (stack ops, handlers, block analysis) are in
 * stackOrderInternalDefsScript.sml.
 *)

Theory stackOrderDefs
Ancestors
  stackOrderInternalDefs

(* Main entry: analyze all successors of lbl, merge their needed lists.
   Returns (merged_needed, updated_from_to).
   Python: get_stack *)
Definition so_get_stack_def:
  so_get_stack cfg lr fn from_to lbl =
    let succs = cfg_succs_of cfg lbl in
    let from_to' =
      FOLDL (so_analyze_succ cfg lr fn) from_to succs in
    let orders = MAP (λsucc.
      case FLOOKUP from_to' (lbl, succ) of
        NONE => []
      | SOME n => n) succs in
    (so_merge orders, from_to')
End

(* Query from_to with liveness extension: extend needed with
   input_vars_from that aren't already included.
   Python: from_to method *)
Definition so_from_to_query_def:
  so_from_to_query lr fn from_to origin_lbl succ_lbl =
    let base = (case FLOOKUP from_to (origin_lbl, succ_lbl) of
                  NONE => []
                | SOME n => n) in
    case lookup_block succ_lbl fn.fn_blocks of
      NONE => base
    | SOME succ_bb =>
        let live_in =
          input_vars_from origin_lbl succ_bb.bb_instructions
            (live_vars_at lr succ_lbl 0) in
        FOLDL (λtgt v.
          if MEM v tgt then tgt else SNOC v tgt)
        base live_in
End

(* The from_to well-formedness invariant: every variable stored in the
   from_to map is live at the entry of the target block.
   Used as the inductive invariant when the DFT threads from_to
   across successive so_get_stack calls. *)
Definition from_to_wf_def:
  from_to_wf lr from_to ⇔
    ∀pred succ ns w.
      FLOOKUP from_to (pred, succ) = SOME ns ∧ MEM w ns ⇒
      MEM w (live_vars_at lr succ 0)
End

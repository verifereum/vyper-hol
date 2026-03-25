(*
 * CFG Well-Formedness Predicates
 *
 * Structural properties of the control flow graph that passes
 * establish or preserve. Separated from venomWf (instruction-level)
 * and cfgTransform (block manipulation helpers).
 *
 * TOP-LEVEL:
 *   all_reachable      — every block reachable from entry
 *   is_normalized_cfg  — no multi-succ → multi-pred edges
 *)

Theory cfgWf
Ancestors
  venomWf cfgTransform

(* All blocks in the function are reachable from the entry. *)
Definition all_reachable_def:
  all_reachable fn ⇔
    ∀bb. MEM bb fn.fn_blocks ⇒ fn_reachable fn bb.bb_label
End

(* Normalized CFG: no edge goes from a multi-successor block to a
   multi-predecessor block. Established by cfg_normalization pass. *)
Definition is_normalized_cfg_def:
  is_normalized_cfg fn ⇔
    ∀bb succ_lbl.
      MEM bb fn.fn_blocks ∧
      MEM succ_lbl (bb_succs bb) ∧
      num_succs bb > 1 ⇒
      num_preds fn succ_lbl ≤ 1
End

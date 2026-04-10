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

(* ==========================================================================
   Function-level PHI / CFG coherence

   These relate PHI operands to the CFG predecessor structure.
   Requires both venomWf (for phi_pairs, inst_wf) and cfgTransform
   (for pred_labels, block_preds).
   ========================================================================== *)

(* Soundness: every label in a PHI references an actual predecessor.
   I.e. PHI operands don't mention blocks that aren't predecessors. *)
Definition fn_phi_preds_sound_def:
  fn_phi_preds_sound func ⇔
    ∀bb inst l v.
      MEM bb func.fn_blocks ∧
      MEM inst bb.bb_instructions ∧
      inst.inst_opcode = PHI ∧
      MEM (l, v) (phi_pairs inst.inst_operands) ⇒
      MEM l (pred_labels func bb.bb_label)
End

(* Completeness: every predecessor of a block with PHIs appears
   in every PHI of that block. *)
Definition fn_phi_preds_complete_def:
  fn_phi_preds_complete func ⇔
    ∀bb inst l.
      MEM bb func.fn_blocks ∧
      MEM inst bb.bb_instructions ∧
      inst.inst_opcode = PHI ∧
      MEM l (pred_labels func bb.bb_label) ⇒
      ∃v. MEM (l, v) (phi_pairs inst.inst_operands)
End

(* Bundle: PHIs exactly mirror CFG predecessors. *)
Definition fn_phi_wf_def:
  fn_phi_wf func ⇔
    fn_phi_preds_sound func ∧ fn_phi_preds_complete func
End

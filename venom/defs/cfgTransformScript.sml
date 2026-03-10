(*
 * CFG Transform Utilities — Definitions
 *
 * Shared infrastructure for passes that modify block topology:
 * simplify_cfg, cfg_normalization, tail_merge.
 *
 * TOP-LEVEL:
 *   remove_block          — remove a block by label
 *   replace_block         — replace a block's content by label
 *   subst_label_op/inst/block/fn — label substitution chain
 *   is_jmp_only           — block is a single unconditional jump
 *   no_phis               — block has no PHI instructions
 *   single_succ_jmp       — block's terminator is JMP to a given label
 *   fn_succ               — CFG edge relation (label → label)
 *   reachable             — label reachable from entry via RTC
 *)

Theory cfgTransform
Ancestors
  venomInst

(* ===== Block List Operations ===== *)

(* Remove all blocks with a given label from a block list. *)
Definition remove_block_def:
  remove_block lbl bbs = FILTER (λbb. bb.bb_label ≠ lbl) bbs
End

(* Replace all blocks matching a label (at most one with ALL_DISTINCT labels). *)
Definition replace_block_def:
  replace_block lbl bb' bbs =
    MAP (λbb. if bb.bb_label = lbl then bb' else bb) bbs
End

(* ===== Label Substitution ===== *)

(* Substitute a label in a single operand. Non-label operands unchanged. *)
Definition subst_label_op_def:
  subst_label_op old new (Label l) =
    (if l = old then Label new else Label l) ∧
  subst_label_op old new (Var v) = Var v ∧
  subst_label_op old new (Lit c) = Lit c
End

(* Substitute a label in an instruction's operands. *)
Definition subst_label_inst_def:
  subst_label_inst old new inst =
    inst with inst_operands :=
      MAP (subst_label_op old new) inst.inst_operands
End

(* Substitute a label in all instructions of a block. *)
Definition subst_label_block_def:
  subst_label_block old new bb =
    bb with bb_instructions :=
      MAP (subst_label_inst old new) bb.bb_instructions
End

(* Substitute a label in all blocks of a function. *)
Definition subst_label_fn_def:
  subst_label_fn old new fn =
    fn with fn_blocks :=
      MAP (subst_label_block old new) fn.fn_blocks
End

(* ===== Block Predicates ===== *)

(* Block is a single unconditional jump instruction. *)
Definition is_jmp_only_def:
  is_jmp_only bb ⇔
    ∃inst lbl.
      bb.bb_instructions = [inst] ∧
      inst.inst_opcode = JMP ∧
      inst.inst_operands = [Label lbl]
End

(* Block has no PHI instructions. *)
Definition no_phis_def:
  no_phis bb ⇔
    EVERY (λinst. inst.inst_opcode ≠ PHI) bb.bb_instructions
End

(* Block's terminator is JMP to the given label. *)
Definition single_succ_jmp_def:
  single_succ_jmp bb lbl ⇔
    bb.bb_instructions ≠ [] ∧
    (LAST bb.bb_instructions).inst_opcode = JMP ∧
    (LAST bb.bb_instructions).inst_operands = [Label lbl]
End

(* ===== CFG Reachability ===== *)

(* CFG edge: a → b iff some block at label a has b as a successor. *)
Definition fn_succ_def:
  fn_succ fn a b ⇔
    ∃bb. lookup_block a fn.fn_blocks = SOME bb ∧
         MEM b (bb_succs bb)
End

(* Label is reachable from the function's entry block via CFG edges. *)
Definition reachable_def:
  reachable fn lbl ⇔
    ∃entry.
      fn_entry_label fn = SOME entry ∧
      RTC (fn_succ fn) entry lbl
End

(* ===== PHI Operand Removal ===== *)

(* Remove the label/value pair for a given predecessor from PHI operands.
   Used when a predecessor block is removed (simplify_cfg unreachable removal).
   PHI operands are structured as [Label l1, val1, Label l2, val2, ...].
   This removes all pairs where the label matches. *)
Definition remove_phi_label_def:
  remove_phi_label lbl [] = [] /\
  remove_phi_label lbl [x] = [x] /\
  remove_phi_label lbl (Label l :: val_op :: rest) =
    (if l = lbl then remove_phi_label lbl rest
     else Label l :: val_op :: remove_phi_label lbl rest) /\
  remove_phi_label lbl (x :: y :: rest) =
    x :: y :: remove_phi_label lbl rest
End

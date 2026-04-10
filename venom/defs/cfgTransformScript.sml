(*
 * CFG Transform Utilities — Definitions
 *
 * Shared infrastructure for passes that modify block topology:
 * simplify_cfg, cfg_normalization, tail_merge.
 *
 * TOP-LEVEL:
 *   remove_block          — remove a block by label
 *   replace_block         — replace a block's content by label
 *   subst_label_op/inst/block/fn — single-pair label substitution
 *   subst_label_terminator — single-pair, terminators only
 *   subst_label_map_op/inst — batch label substitution primitives
 *   subst_block_labels_inst/block/fn — batch substitution, block-refs only
 *     (restricts to terminators + PHI; leaves INVOKE/OFFSET alone)
 *   is_jmp_only           — block is a single unconditional jump
 *   no_phis               — block has no PHI instructions
 *   single_succ_jmp       — block's terminator is JMP to a given label
 *   fn_succ               — CFG edge relation (label → label)
 *   reachable             — label reachable from entry via RTC
 *   is_halting_opcode     — opcode halts execution
 *   bb_is_halting         — block ends with halting opcode
 *   block_preds           — predecessor blocks of a label
 *   num_preds             — number of predecessors
 *   num_succs             — number of successors
 *   fn_all_vars           — all variable names in a function
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

(* Substitute a label only in terminator instructions of a block.
   Non-terminator instructions (including PHIs) are left unchanged.
   Matches Python's replace_label_operands on the last instruction only. *)
Definition subst_label_terminator_def:
  subst_label_terminator old new bb =
    bb with bb_instructions :=
      MAP (λinst.
        if is_terminator inst.inst_opcode
        then subst_label_inst old new inst
        else inst)
      bb.bb_instructions
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

(* ===== Batch Label Substitution ===== *)

(* Apply a label map (assoc list) to a single operand.
   Unlike subst_label_op (single old→new), this applies all
   substitutions in one pass. *)
Definition subst_label_map_op_def:
  subst_label_map_op label_map (Label l) =
    (case ALOOKUP label_map l of
       SOME new_l => Label new_l
     | NONE => Label l) ∧
  subst_label_map_op label_map (Var v) = Var v ∧
  subst_label_map_op label_map (Lit w) = Lit w
End

Definition subst_label_map_inst_def:
  subst_label_map_inst label_map inst =
    inst with inst_operands :=
      MAP (subst_label_map_op label_map) inst.inst_operands
End

(* Batch label substitution restricted to block-referencing instructions.
   Only substitutes in instructions where is_block_label_opcode holds
   (terminators + PHI). Leaves INVOKE, OFFSET, CALLOCA etc. untouched. *)
Definition subst_block_labels_inst_def:
  subst_block_labels_inst label_map inst =
    if is_block_label_opcode inst.inst_opcode
    then subst_label_map_inst label_map inst
    else inst
End

Definition subst_block_labels_block_def:
  subst_block_labels_block label_map bb =
    bb with bb_instructions :=
      MAP (subst_block_labels_inst label_map) bb.bb_instructions
End

Definition subst_block_labels_fn_def:
  subst_block_labels_fn label_map func =
    func with fn_blocks :=
      MAP (subst_block_labels_block label_map) func.fn_blocks
End

(* NOTE: Python _replace_all_labels also updates ctx.data_segment label
   references. Deferred until venom_to_bytecode is specified — data segment
   label resolution depends on bytecode layout (see lower_dload pass). *)

(* ===== Halting Block Detection ===== *)

(* Halting opcodes: execution stops, no control flow successor.
   Matches Python HALTING_TERMINATORS. *)
Definition is_halting_opcode_def:
  is_halting_opcode RETURN = T ∧
  is_halting_opcode REVERT = T ∧
  is_halting_opcode STOP = T ∧
  is_halting_opcode INVALID = T ∧
  is_halting_opcode SELFDESTRUCT = T ∧
  is_halting_opcode _ = F
End

(* Block ends with a halting instruction. *)
Definition bb_is_halting_def:
  bb_is_halting bb ⇔
    bb.bb_instructions ≠ [] ∧
    is_halting_opcode (LAST bb.bb_instructions).inst_opcode
End

(* ===== Predecessor/Successor Counts ===== *)

(* Predecessor blocks of a given label within a function. *)
Definition block_preds_def:
  block_preds func lbl =
    FILTER (λbb. MEM lbl (bb_succs bb)) func.fn_blocks
End

(* Predecessor labels of a given label. *)
Definition pred_labels_def:
  pred_labels func lbl =
    MAP (λbb. bb.bb_label) (block_preds func lbl)
End

(* Number of predecessors. *)
Definition num_preds_def:
  num_preds func lbl = LENGTH (block_preds func lbl)
End

(* Number of successors of a block. *)
Definition num_succs_def:
  num_succs bb = LENGTH (bb_succs bb)
End

(* All variable names in a function (outputs + operand vars). *)
Definition fn_all_vars_def:
  fn_all_vars func =
    FLAT (MAP (λbb.
      FLAT (MAP (λinst.
        inst.inst_outputs ++
        FLAT (MAP (λop. case op of Var v => [v] | _ => [])
                  inst.inst_operands))
      bb.bb_instructions))
    func.fn_blocks)
End

(* ===== Instruction ID Renumbering ===== *)

(* Assign sequential IDs to instructions within a block, starting from n.
   Returns (next_id, updated_block). *)
Definition renumber_block_inst_ids_def:
  renumber_block_inst_ids n bb =
    let (n', insts') = FOLDL (λ(id, acc) inst.
      (id + 1n, acc ++ [inst with inst_id := id]))
      (n, []) bb.bb_instructions in
    (n', bb with bb_instructions := insts')
End

(* Assign sequential IDs to all instructions across all blocks.
   Threads the counter so IDs are globally unique.
   Establishes fn_inst_ids_distinct by construction. *)
Definition renumber_fn_inst_ids_def:
  renumber_fn_inst_ids func =
    let (_, bbs') = FOLDL (λ(n, acc) bb.
      let (n', bb') = renumber_block_inst_ids n bb in
      (n', acc ++ [bb']))
      (0n, []) func.fn_blocks in
    func with fn_blocks := bbs'
End

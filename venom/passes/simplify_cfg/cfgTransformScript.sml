(*
 * SimplifyCFG Transformation Definitions
 *
 * This theory defines the CFG simplification transformation.
 * The pass merges blocks and threads jumps to simplify the control flow graph.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL DEFINITIONS:
 *   - merge_blocks          : Merge two consecutive blocks
 *   - is_unconditional_jump : Check if block ends with unconditional jump
 *   - is_passthrough_block  : Check if block is just a jump
 *   - thread_jump           : Thread a jump through a passthrough block
 *   - simplify_cfg_step     : Single simplification step
 *
 * HELPER DEFINITIONS:
 *   - replace_label         : Replace label in operands
 *   - update_phi_labels     : Update PHI instructions after merge
 *   - get_jump_target       : Get target of unconditional jump
 *
 * ============================================================================
 *)

Theory cfgTransform
Ancestors
  list finite_map pred_set
  venomState venomInst venomSem

(* ==========================================================================
   CFG Analysis Helpers
   ========================================================================== *)

(* Get the terminator instruction of a block (last instruction) *)
Definition get_terminator_def:
  get_terminator bb =
    if NULL bb.bb_instructions then NONE
    else SOME (LAST bb.bb_instructions)
End

(* Check if an instruction is an unconditional jump *)
Definition is_jmp_inst_def:
  is_jmp_inst inst <=> inst.inst_opcode = JMP
End

(* Get the target label of a JMP instruction.
   Only returns SOME if both the opcode is JMP and the operands are [Label lbl]. *)
Definition get_jmp_target_def:
  get_jmp_target inst =
    if is_jmp_inst inst then
      case inst.inst_operands of
        [Label lbl] => SOME lbl
      | _ => NONE
    else NONE
End

(* Check if a block ends with an unconditional jump *)
Definition is_unconditional_jump_def:
  is_unconditional_jump bb =
    case get_terminator bb of
      NONE => F
    | SOME inst => is_jmp_inst inst
End

(* Get the target of a block's unconditional jump *)
Definition get_block_target_def:
  get_block_target bb =
    case get_terminator bb of
      NONE => NONE
    | SOME inst => get_jmp_target inst
End

(* Check if a block is a passthrough (single instruction that is a JMP) *)
Definition is_passthrough_block_def:
  is_passthrough_block bb <=>
    LENGTH bb.bb_instructions = 1 /\
    is_unconditional_jump bb
End

(* ==========================================================================
   Label Replacement
   ========================================================================== *)

(* Replace old_lbl with new_lbl in an operand *)
Definition replace_label_operand_def:
  replace_label_operand old_lbl new_lbl (Label l) =
    (if l = old_lbl then Label new_lbl else Label l) /\
  replace_label_operand old_lbl new_lbl (Lit v) = Lit v /\
  replace_label_operand old_lbl new_lbl (Var x) = Var x
End

(* Replace labels in an instruction's operands *)
Definition replace_label_inst_def:
  replace_label_inst old_lbl new_lbl inst =
    inst with inst_operands := MAP (replace_label_operand old_lbl new_lbl) inst.inst_operands
End

(* Replace labels in all instructions of a block *)
Definition replace_label_block_def:
  replace_label_block old_lbl new_lbl bb =
    bb with bb_instructions := MAP (replace_label_inst old_lbl new_lbl) bb.bb_instructions
End

(* ==========================================================================
   PHI Instruction Handling
   ========================================================================== *)

(* Check if instruction is a PHI *)
Definition is_phi_inst_def:
  is_phi_inst inst <=> inst.inst_opcode = PHI
End

(* Get label operands from PHI instruction (every other operand starting at 0) *)
Definition phi_labels_def:
  phi_labels [] = [] /\
  phi_labels [_] = [] /\
  phi_labels (Label l :: _ :: rest) = l :: phi_labels rest /\
  phi_labels (_ :: _ :: rest) = phi_labels rest
End

(* ==========================================================================
   Block Merging
   ========================================================================== *)

(* Merge block B into block A (A's terminator is removed, B's instructions appended)
   Precondition: A ends with unconditional jump to B, B has no PHIs *)
Definition merge_blocks_def:
  merge_blocks a b =
    a with bb_instructions :=
      (FRONT a.bb_instructions) ++ b.bb_instructions
End

(* ==========================================================================
   CFG Helpers
   ========================================================================== *)

(* Get all successor labels of a block *)
Definition get_successors_def:
  get_successors bb =
    case get_terminator bb of
      NONE => []
    | SOME inst => FILTER IS_SOME (MAP get_label inst.inst_operands)
End

(* Count how many blocks jump to a given label *)
Definition count_predecessors_def:
  count_predecessors target blocks =
    LENGTH (FILTER (\bb. MEM (SOME target) (MAP get_label
      (case get_terminator bb of NONE => [] | SOME inst => inst.inst_operands)))
      blocks)
End

(* Check if a block has a single predecessor *)
Definition has_single_predecessor_def:
  has_single_predecessor target blocks <=>
    (count_predecessors target blocks = 1)
End

(* ==========================================================================
   Simplification Predicates
   ========================================================================== *)

(* Can we merge block A with its successor B?
   Conditions:
   1. A ends with unconditional jump to B
   2. B has exactly one predecessor (A)
   3. B has no PHI instructions (since PHIs need multiple predecessors) *)
Definition can_merge_blocks_def:
  can_merge_blocks a b blocks <=>
    get_block_target a = SOME b.bb_label /\
    has_single_predecessor b.bb_label blocks /\
    ~EXISTS is_phi_inst b.bb_instructions
End

(* Can we thread through block B?
   Conditions:
   1. B is a passthrough block (single JMP instruction)
   2. Threading won't create issues with PHIs *)
Definition can_thread_jump_def:
  can_thread_jump b <=>
    is_passthrough_block b
End

(* ==========================================================================
   Jump Threading Transformation
   ========================================================================== *)

(* Thread jumps through a passthrough block:
   If A jumps to B, and B is just "jmp C", rewrite A to jump to C directly *)
Definition thread_jump_inst_def:
  thread_jump_inst passthrough_lbl target_lbl inst =
    inst with inst_operands :=
      MAP (\op. case op of
                  Label l => if l = passthrough_lbl then Label target_lbl else Label l
                | _ => op)
          inst.inst_operands
End

Definition thread_jump_block_def:
  thread_jump_block passthrough_lbl target_lbl bb =
    bb with bb_instructions :=
      MAP (thread_jump_inst passthrough_lbl target_lbl) bb.bb_instructions
End

(* ==========================================================================
   Block Removal
   ========================================================================== *)

(* Remove a block by label *)
Definition remove_block_def:
  remove_block lbl blocks =
    FILTER (\bb. bb.bb_label <> lbl) blocks
End

(* ==========================================================================
   Single Transformation Steps
   ========================================================================== *)

(* Apply a single merge transformation to a function *)
Definition apply_merge_def:
  apply_merge a_lbl b_lbl fn =
    case (lookup_block a_lbl fn.fn_blocks, lookup_block b_lbl fn.fn_blocks) of
      (SOME a, SOME b) =>
        let merged = merge_blocks a b in
        let blocks' = remove_block b_lbl fn.fn_blocks in
        let blocks'' = MAP (\bb. if bb.bb_label = a_lbl then merged else bb) blocks' in
        (* Update PHI labels in successors *)
        let blocks''' = MAP (replace_label_block b_lbl a_lbl) blocks'' in
        SOME (fn with fn_blocks := blocks''')
    | _ => NONE
End

(* Apply a single thread transformation to a function *)
Definition apply_thread_def:
  apply_thread passthrough_lbl target_lbl fn =
    case lookup_block passthrough_lbl fn.fn_blocks of
      SOME b =>
        if is_passthrough_block b then
          let blocks' = MAP (thread_jump_block passthrough_lbl target_lbl) fn.fn_blocks in
          (* Remove the passthrough block if it's now unreachable *)
          let blocks'' = remove_block passthrough_lbl blocks' in
          SOME (fn with fn_blocks := blocks'')
        else NONE
    | NONE => NONE
End

(* ==========================================================================
   Transformation Properties
   ========================================================================== *)

(* Merge preserves block count (minus one) *)
Theorem merge_blocks_length:
  !a b.
    LENGTH (merge_blocks a b).bb_instructions =
    LENGTH (FRONT a.bb_instructions) + LENGTH b.bb_instructions
Proof
  rw[merge_blocks_def]
QED

(* Merge preserves the label of block A *)
Theorem merge_blocks_label:
  !a b. (merge_blocks a b).bb_label = a.bb_label
Proof
  rw[merge_blocks_def]
QED

(* Replace label preserves block label *)
Theorem replace_label_block_label:
  !old new bb. (replace_label_block old new bb).bb_label = bb.bb_label
Proof
  rw[replace_label_block_def]
QED

(* Replace label preserves instruction count *)
Theorem replace_label_block_length:
  !old new bb.
    LENGTH (replace_label_block old new bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  rw[replace_label_block_def, LENGTH_MAP]
QED

(* Thread jump preserves block label *)
Theorem thread_jump_block_label:
  !pl tl bb. (thread_jump_block pl tl bb).bb_label = bb.bb_label
Proof
  rw[thread_jump_block_def]
QED

(* Thread jump preserves instruction count *)
Theorem thread_jump_block_length:
  !pl tl bb.
    LENGTH (thread_jump_block pl tl bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  rw[thread_jump_block_def, LENGTH_MAP]
QED

(* Get terminator of merged block is terminator of b *)
Theorem merge_blocks_terminator:
  !a b.
    a.bb_instructions <> [] /\
    b.bb_instructions <> [] ==>
    get_terminator (merge_blocks a b) = get_terminator b
Proof
  rw[merge_blocks_def, get_terminator_def, NULL_EQ] >>
  Cases_on `FRONT a.bb_instructions` >> simp[] >>
  Cases_on `b.bb_instructions` >> fs[] >>
  simp[LAST_DEF]
QED

(* ==========================================================================
   Lookup Helpers
   ========================================================================== *)

Theorem lookup_block_remove:
  !lbl lbl' blocks.
    lbl <> lbl' ==>
    lookup_block lbl (remove_block lbl' blocks) = lookup_block lbl blocks
Proof
  Induct_on `blocks` >- simp[lookup_block_def, remove_block_def] >>
  rw[remove_block_def] >-
    (simp[lookup_block_def] >> Cases_on `h.bb_label = lbl` >> simp[] >>
     first_x_assum (qspecl_then [`lbl`, `lbl'`] mp_tac) >> simp[remove_block_def]) >>
  simp[lookup_block_def] >>
  first_x_assum (qspecl_then [`lbl`, `h.bb_label`] mp_tac) >> simp[remove_block_def]
QED

Theorem lookup_block_map:
  !lbl blocks f.
    (!bb. (f bb).bb_label = bb.bb_label) ==>
    lookup_block lbl (MAP f blocks) = OPTION_MAP f (lookup_block lbl blocks)
Proof
  Induct_on `blocks` >> rw[lookup_block_def] >>
  Cases_on `h.bb_label = lbl` >> simp[]
QED


(*
 * Tail Merge Helpers — subst_block_labels structural lemmas.
 *
 * subst_block_labels_inst only modifies instructions where
 * is_block_label_opcode holds (terminators + PHI).
 * Non-block-label instructions pass through unchanged.
 *)

Theory tailMergeHelpers
Ancestors
  tailMergeDefs stateEquiv venomExecSemantics
Libs
  cfgTransformTheory venomStateTheory venomExecSemanticsTheory venomInstTheory
  tailMergeDefsTheory stateEquivTheory

(* ================================================================
   subst_label_map primitives (still used by subst_block_labels)
   ================================================================ *)

Theorem eval_operand_subst_var[simp]:
  !m v s. eval_operand (subst_label_map_op m (Var v)) s = eval_operand (Var v) s
Proof
  simp[subst_label_map_op_def]
QED

Theorem eval_operand_subst_lit[simp]:
  !m w s. eval_operand (subst_label_map_op m (Lit w)) s = eval_operand (Lit w) s
Proof
  simp[subst_label_map_op_def]
QED

Theorem subst_label_map_op_var[simp]:
  !m v. subst_label_map_op m (Var v) = Var v
Proof
  simp[subst_label_map_op_def]
QED

Theorem subst_label_map_op_lit[simp]:
  !m w. subst_label_map_op m (Lit w) = Lit w
Proof
  simp[subst_label_map_op_def]
QED

Theorem subst_label_map_inst_opcode[simp]:
  !m inst. (subst_label_map_inst m inst).inst_opcode = inst.inst_opcode
Proof
  simp[subst_label_map_inst_def]
QED

Theorem subst_label_map_inst_outputs[simp]:
  !m inst. (subst_label_map_inst m inst).inst_outputs = inst.inst_outputs
Proof
  simp[subst_label_map_inst_def]
QED

Theorem subst_label_map_inst_operands:
  !m inst. (subst_label_map_inst m inst).inst_operands =
           MAP (subst_label_map_op m) inst.inst_operands
Proof
  simp[subst_label_map_inst_def]
QED

(* ================================================================
   subst_block_labels structural preservation
   ================================================================ *)

Theorem subst_block_labels_inst_id[simp]:
  !m inst. ~is_block_label_opcode inst.inst_opcode ==>
    subst_block_labels_inst m inst = inst
Proof
  simp[subst_block_labels_inst_def]
QED

Theorem subst_block_labels_inst_opcode[simp]:
  !m inst. (subst_block_labels_inst m inst).inst_opcode = inst.inst_opcode
Proof
  rw[subst_block_labels_inst_def]
QED

Theorem subst_block_labels_inst_outputs[simp]:
  !m inst. (subst_block_labels_inst m inst).inst_outputs = inst.inst_outputs
Proof
  rw[subst_block_labels_inst_def, subst_label_map_inst_def]
QED

Theorem subst_block_labels_block_label[simp]:
  !m bb. (subst_block_labels_block m bb).bb_label = bb.bb_label
Proof
  simp[subst_block_labels_block_def]
QED

Theorem get_instruction_subst_block_labels:
  !m bb idx.
    get_instruction (subst_block_labels_block m bb) idx =
    OPTION_MAP (subst_block_labels_inst m) (get_instruction bb idx)
Proof
  rw[get_instruction_def, subst_block_labels_block_def] >>
  simp[listTheory.EL_MAP]
QED

(* Non-block-label instruction: step_inst_base unchanged *)
Theorem step_inst_base_subst_block_labels_id:
  !m inst s.
    ~is_block_label_opcode inst.inst_opcode ==>
    step_inst_base (subst_block_labels_inst m inst) s =
    step_inst_base inst s
Proof
  simp[subst_block_labels_inst_def]
QED

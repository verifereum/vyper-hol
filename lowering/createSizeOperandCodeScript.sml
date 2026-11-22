(* Branch confinement for completed expression operands. *)
Theory createSizeOperandCode
Ancestors
  createSizeOperandMutual createSizePreparationCode createSizeLocationCode
  createSizeCutCode exprLowering

Theorem create_operand_cut_code:
  (!ce ty e a. create_cut_code {} a (SND (compile_expr ce ty e a))) /\
  (!ce ty e a. create_cut_code {} a (SND (lower_value compile_expr ce ty e a)))
Proof
  conj_asm1_tac
  >- (mp_tac create_operand_mutual_if_create >> simp[create_create_call_cut_code]) >>
  simp[lower_value_def] >> rpt gen_tac >>
  irule create_cut_code_bind >> simp[create_unwrap_cut_code]
QED

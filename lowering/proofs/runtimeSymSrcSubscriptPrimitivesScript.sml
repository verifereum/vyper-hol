Theory runtimeSymSrcSubscriptPrimitives
Ancestors
  runtimeSymSrcContext runtimeSymSrcEmission exprLowering compileEnv
  emitHelper loweringShapeDefs venomInst stackPlanTypes list

Theorem runtime_sym_keccak256_key:
  EVERY runtime_sym_inst (state_insts s) /\ ~is_label_operand op /\
  compile_keccak256_key op b s = (out,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out
Proof
  Cases_on `b` >>
  simp[compile_keccak256_key_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 2 (pairarg_tac >> simp[]) >> strip_tac >> gvs[]
  >- (drule_at (Pat `compile_alloc_buffer _ _ = _`) runtime_sym_alloc_buffer >>
      simp[] >> strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
      simp[] >> strip_tac >>
      drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
      simp[is_label_operand_def]) >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[] >> strip_tac >>
  qpat_assum `emit_op SHA3 _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]
QED

Theorem runtime_sym_mapping_subscript:
  EVERY runtime_sym_inst (state_insts s) /\
  ~is_label_operand bop /\ ~is_label_operand key /\
  compile_mapping_subscript bop key s = (out,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out
Proof
  simp[compile_mapping_subscript_def, comp_bind_def, comp_ignore_bind_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule_at (Pat `compile_alloc_buffer _ _ = _`) runtime_sym_alloc_buffer >>
  simp[] >> strip_tac >>
  qpat_assum `emit_void MSTORE [_; bop] _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[] >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_void MSTORE [_; key] _ = _` (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[] >> strip_tac >>
  qpat_assum `emit_op SHA3 _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def]
QED

Theorem runtime_sym_tuple_subscript:
  EVERY runtime_sym_inst (state_insts s) /\ ~is_label_operand bop /\
  compile_tuple_subscript bop off s = (out,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out
Proof
  simp[compile_tuple_subscript_def] >> strip_tac >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def]
QED

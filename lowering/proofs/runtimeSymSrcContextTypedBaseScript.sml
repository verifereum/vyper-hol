Theory runtimeSymSrcContextTypedBase
Ancestors
  runtimeSymSrcContext runtimeSymSrcEmission context compileEnv emitHelper loweringShapeDefs
  venomInst stackPlanTypes list

Theorem runtime_sym_with_byte_offset:
  ~is_label_operand base_op /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_with_byte_offset base_op off s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, comp_return_def] >> strip_tac >> gvs[] >>
  qpat_assum `emit_op _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def]
QED

Theorem runtime_sym_copy_memory_dynamic:
  ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand len /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_copy_memory_dynamic dst src len s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_copy_memory_dynamic_def] >> strip_tac >>
  qpat_assum `emit_void _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED

Theorem runtime_sym_bytestring_copy_len:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_bytestring_copy_len src s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_bytestring_copy_len_def, comp_bind_def] >>
  ntac 4 (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_assum `emit_op MLOAD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_op NOT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op ADD [_; Lit 31w] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op AND _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ADD [_; Lit 32w] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[is_label_operand_def]
QED

Theorem runtime_sym_store_bytestring:
  ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_bytestring src dst s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[compile_store_bytestring_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qpat_assum `compile_bytestring_copy_len _ _ = _`
    (mp_then Any mp_tac runtime_sym_bytestring_copy_len) >> simp[] >> strip_tac >>
  qpat_assum `emit_void _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED

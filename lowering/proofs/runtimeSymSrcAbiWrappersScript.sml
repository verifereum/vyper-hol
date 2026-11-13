Theory runtimeSymSrcAbiWrappers
Ancestors
  runtimeSymSrcAbiEncode runtimeSymSrcAbiDecode runtimeSymSrcContext
  runtimeSymSrcEmission runtimeSymSrcInterfaces builtinAbi compileEnv
  emitHelper loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_lower_abi_encode:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  lower_abi_encode (ensure : bool) mid src info n s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `mid` >>
  simp[lower_abi_encode_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac
  >- (drule_all runtime_sym_abi_encode_to_buf >> strip_tac >>
      rev_dxrule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  qpat_x_assum `emit_op ADD [_; Lit 32w] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_x_assum `emit_void MSTORE [_; Lit _] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_abi_encode_to_buf >> strip_tac >>
  rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]
QED

Theorem runtime_sym_lower_abi_decode:
  ~is_label_operand src /\ EVERY runtime_sym_inst (state_insts s) /\
  lower_abi_decode src info lo hi out_size s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `lo = hi` >>
  simp[lower_abi_decode_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  ntac 2 (rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
          simp[is_label_operand_def] >> strip_tac)
  >- (rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
      simp[is_label_operand_def] >> strip_tac >>
      rev_dxrule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
      simp[] >> strip_tac >>
      drule_all runtime_sym_alloc_buffer >> strip_tac >>
      qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_abi_decode_to_buf) >>
      simp[is_label_operand_def]) >>
  ntac 5 (rev_dxrule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
  simp[] >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_abi_decode_to_buf) >>
      simp[is_label_operand_def]
QED

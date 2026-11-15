Theory runtimeSymSrcDynarrayPop
Ancestors
  runtimeSymSrcContext runtimeSymSrcEmission exprLowering compileEnv
  emitHelper loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_dynarray_pop:
  ~is_label_operand base_op /\
  (!v. imm = SOME v ==> ~is_label_operand v) /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_dynarray_pop base_op ws elem_size ctor imm loc s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_dynarray_pop_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_assum `compile_ptr_load _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_ptr_load) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ISZERO _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_x_assum `emit_op ISZERO _ _ = _` kall_tac >>
  qpat_assum `emit_op ISZERO _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_void ASSERT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[] >> strip_tac >>
  qpat_assum `emit_op SUB _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
    simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `compile_ptr_store _ _ _ _ _ _ = _`
    (mp_then Any mp_tac runtime_sym_ptr_store) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ADD [base_op; _] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
    simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op MUL _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
    simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = (op,s')`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]
QED

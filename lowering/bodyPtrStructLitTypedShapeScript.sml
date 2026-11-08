Theory bodyPtrStructLitTypedShape
Ancestors loweringShapeProps loweringShapeRules loweringShapeDefs context
  compileEnv venomInst unitShapeDefs stackPlanTypes

Theorem structlit_typed_word_shape[local]:
  shape_step internal compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (do v <- emit_op MLOAD [src]; emit_void MSTORE [dst; v] od)
    (\u s. T)
Proof
  Cases_on `is_label_operand src` >- simp[shape_step_def, plain_operand_def] >>
  Cases_on `is_label_operand dst` >- simp[shape_step_def, plain_operand_def] >>
  irule shape_step_bind >>
  qexists `\v s. plain_operand s dst /\ plain_operand s v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_emit_op >>
      qexistsl [`\s. plain_operand s dst`, `compiler_label`] >>
      simp[SRULE [] (Q.SPEC `[p]` shape_stable_plain_operands),
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def, label_or_plain_def]) >>
  gen_tac >> BETA_TAC >> irule shape_step_emit_void_pre >>
  simp[plain_operand_def, shape_stable_def, lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
    inst_shape_ok_def, inst_jump_labels_ok_def, is_param_opcode_def,
    is_read0_opcode_def, label_positions_ok_def, is_terminator_def, label_or_plain_def]
QED

Theorem structlit_copy_memory_shape[local]:
  shape_step internal compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (compile_copy_memory dst src n) (\u s. T)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def, shape_step_return] >>
  irule shape_step_emit_void_pre >>
  simp[plain_operand_def, label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, is_label_operand_def]
QED

Theorem structlit_typed_store_unequal_shape:
  dt <> st ==>
  shape_step internal compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (compile_store_memory_typed ce dst dt src st) (\u s. T)
Proof
  strip_tac >> Cases_on `is_word_type dt`
  >- simp[Once compile_store_memory_typed_def, structlit_typed_word_shape] >>
  Cases_on `is_bytestring_type dt`
  >- (simp[Once compile_store_memory_typed_def] >>
      Cases_on `is_bytestring_type st`
      >- (mp_tac (Q.SPECL [`ce`, `src`, `dst`, `dt`, `st`, `internal`]
            compile_store_memory_shape) >> simp[compile_store_memory_def]) >> simp[] >>
      Cases_on `acyclic_struct_metadata ce.ce_struct_fields` >> simp[]
      >- (Cases_on `dt` >> gvs[is_bytestring_type_def] >>
          Cases_on `st` >> simp[structlit_copy_memory_shape]) >>
      irule shape_step_conseq >> irule_at Any shape_step_emit_void >>
      qexistsl [`\s. T`, `compiler_label`] >>
      simp[shape_stable_def, lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
        inst_shape_ok_def, inst_jump_labels_ok_def, is_param_opcode_def,
        is_read0_opcode_def, label_positions_ok_def, is_terminator_def]) >>
  mp_tac (Q.SPECL [`ce`, `src`, `dst`, `dt`, `st`, `internal`]
    compile_store_memory_shape) >> simp[compile_store_memory_def]
QED

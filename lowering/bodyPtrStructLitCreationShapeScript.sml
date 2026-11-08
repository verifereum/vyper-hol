Theory bodyPtrStructLitCreationShape
Ancestors loweringShapeProps loweringShapeRules loweringShapeDefs
  exprLowering builtinCreate context compileEnv venomInst stackPlanTypes unitShapeDefs


Theorem create_copy_memory_dynamic_shape:
  shape_step internal compiler_label
    (\s. plain_operand s dst /\ plain_operand s src /\ plain_operand s len)
    (compile_copy_memory_dynamic dst src len) (\u s. T)
Proof
  simp[compile_copy_memory_dynamic_def] >> irule shape_step_emit_void_pre >>
  simp[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
       raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
       is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
       is_terminator_def, plain_operand_def, is_label_operand_def]
QED

Theorem create_slot_to_memory_shape:
  loc = LocStorage \/ loc = LocTransient ==>
  shape_step internal compiler_label
    (\s. plain_operand s src /\ plain_operand s dst)
    (compile_slot_to_memory src dst n loc) (\u s. T)
Proof
  strip_tac >> simp[compile_slot_to_memory_def] >>
  irule compile_word_copy_loop_shape >> simp[]
QED

Theorem create_blueprint_check_shape:
  shape_step internal compiler_label
    (\s. plain_operand s target /\ plain_operand s offset)
    (compile_create_blueprint_check target offset) (\v s. plain_operand s v)
Proof
  simp[compile_create_blueprint_check_def] >> irule shape_step_bind >>
  qexists `\x s. plain_operand s offset /\ plain_operand s x` >> reverse conj_tac
  >- (qspecl_then [`internal`, `compiler_label`, `compiler_label`] irule shape_step_conseq >>
      irule_at Any shape_step_frame >>
      irule_at Any shape_step_emit_op_pre >>
      qexistsl [`\s. plain_operand s offset`,
        `\s. plain_operand s target /\ plain_operand s offset`] >>
      simp[SRULE [] (Q.SPEC `[offset]` shape_stable_plain_operands),
        label_or_plain_def, plain_operand_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def, is_label_operand_def]) >>
  qx_gen_tac `x` >> simp[] >> irule shape_step_bind >>
  qexists `\y s. plain_operand s y` >> reverse conj_tac
  >- (irule shape_step_emit_op_pre >>
      simp[label_or_plain_def, plain_operand_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def]) >>
  qx_gen_tac `y` >> simp[] >> irule shape_step_bind >>
  qexists `\z s. plain_operand s y /\ plain_operand s z` >> reverse conj_tac
  >- (qspecl_then [`internal`, `compiler_label`, `compiler_label`] irule shape_step_conseq >>
      irule_at Any shape_step_frame >>
      irule_at Any shape_step_emit_op_pre >>
      qexistsl [`\s. plain_operand s y`, `\s. plain_operand s y`] >>
      simp[SRULE [] (Q.SPEC `[y]` shape_stable_plain_operands),
        label_or_plain_def, plain_operand_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def, is_label_operand_def]) >>
  qx_gen_tac `z` >> simp[] >> irule shape_step_ignore_bind >>
  qexists `\u s. plain_operand s y` >> reverse conj_tac
  >- (qspecl_then [`internal`, `compiler_label`, `compiler_label`] irule shape_step_conseq >>
      irule_at Any shape_step_frame >>
      irule_at Any shape_step_emit_void_pre >>
      qexistsl [`\s. plain_operand s y`,
        `\s. plain_operand s y /\ plain_operand s z`] >>
      simp[SRULE [] (Q.SPEC `[y]` shape_stable_plain_operands),
        label_or_plain_def, plain_operand_def, lowered_inst_ok_def, mk_inst_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def]) >>
  simp[shape_step_return]
QED

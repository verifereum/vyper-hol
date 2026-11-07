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

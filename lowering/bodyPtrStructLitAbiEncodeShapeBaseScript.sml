Theory bodyPtrStructLitAbiEncodeShapeBase
Ancestors bodyPtrStructLitTargetScalar bodyPtrStructLitAbiPrefixProbe
  loweringShapeProps loweringShapeRules loweringShapeDefs abiEncoder
  context compileEnv venomInst stackPlanTypes unitShapeDefs

Theorem abi_encode_static_shape:
  shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (compile_abi_encode_static dst src) (\len s. plain_operand s len)
Proof
  simp[compile_abi_encode_static_def] >> irule target_scalar_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[dst]` shape_stable_plain_operands),
    SRULE [] (Q.SPEC `[src]` shape_stable_plain_operands)] >>
  gen_tac >> irule shape_step_ignore_bind >> qexists `\u s. T` >> reverse conj_tac
  >- (irule shape_step_emit_void_pre >>
      simp[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def, plain_operand_def, is_label_operand_def]) >>
  gen_tac >> irule shape_step_return >>
  simp[plain_operand_def, is_label_operand_def]
QED

Theorem abi_encode_static_info_shape:
  shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (compile_abi_encode_static_info dst src info) (\len s. plain_operand s len)
Proof
  Cases_on `info` >> simp[compile_abi_encode_static_info_def, abi_encode_static_shape] >>
  TRY (irule shape_step_return >> simp[plain_operand_def, is_label_operand_def] >> NO_TAC) >>
  mp_tac abi_prefix_copy_shape >> simp[Once compile_abi_encode_child_def]
QED

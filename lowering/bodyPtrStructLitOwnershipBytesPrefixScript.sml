Theory bodyPtrStructLitOwnershipBytesPrefix
Ancestors bodyPtrStructLitOwnershipConvert bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  loweringShapeDefs loweringShapeRules loweringShapeProps builtinBytes compileEnv
  venomInst unitShapeDefs stackPlanTypes list

Theorem bytestring_src_shape:
  shape_step F compiler_label (\s. plain_operand s src)
    (compile_bytestring_src src)
    (\v s. EVERY (plain_operand s) [FST v; SND v])
Proof
  simp[compile_bytestring_src_def] >> irule shape_step_bind >>
  qexists `\x s. plain_operand s src /\ plain_operand s x` >> reverse conj_tac
  >- (qspecl_then [`F`, `compiler_label`, `compiler_label`] irule shape_step_conseq >>
      irule_at Any shape_step_frame >> irule_at Any shape_step_emit_op_pre >>
      qexistsl [`\s. plain_operand s src`, `\s. plain_operand s src`] >>
      simp[SRULE [] (Q.SPEC `[src]` shape_stable_plain_operands),
        SRULE [] (Q.SPEC `[x]` shape_stable_plain_operands), plain_operand_def,
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def, label_or_plain_def]) >>
  gen_tac >> simp[] >> irule shape_step_bind >>
  qexists `\y s. plain_operand s x /\ plain_operand s y` >> reverse conj_tac
  >- (qspecl_then [`F`, `compiler_label`, `compiler_label`] irule shape_step_conseq >>
      irule_at Any shape_step_frame >> irule_at Any shape_step_emit_op_pre >>
      qexistsl [`\s. plain_operand s x`,
        `\s. plain_operand s src /\ plain_operand s x`] >>
      simp[SRULE [] (Q.SPEC `[src]` shape_stable_plain_operands),
        SRULE [] (Q.SPEC `[x]` shape_stable_plain_operands), plain_operand_def,
        lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
        inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
        label_positions_ok_def, is_terminator_def, label_or_plain_def,
        is_label_operand_def]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[]
QED

Theorem alloc_run_bytestring_src_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s src)
    (compile_bytestring_src src)
    (\v s. shape_state s /\ R s /\ EVERY (plain_operand s) [FST v; SND v])
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  simp[alloc_run_compile_bytestring_src, bytestring_src_shape]
QED

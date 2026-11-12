Theory bodyPtrStructLitOwnershipSlicePrefix
Ancestors bodyPtrStructLitOwnershipCalldataSlice bodyPtrStructLitOwnershipBytesPrefix
  bodyPtrStructLitOwnershipStructFrame loweringShapeDefs loweringShapeRules
  loweringShapeProps builtinBytes compileEnv venomInst unitShapeDefs stackPlanTypes list

Theorem slice_out_buf_shape:
  shape_step F compiler_label (\s. T) (compile_slice_out_buf out_size)
    (\v s. EVERY (plain_operand s) [FST v; SND v])
Proof
  simp[compile_slice_out_buf_def] >> irule shape_step_bind >>
  qexists `\b s. plain_operand s b.buf_operand` >> reverse conj_tac
  >- simp[compile_alloc_buffer_shape] >>
  qx_gen_tac `buf` >>
  CONV_TAC (LAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[Once comp_bind_def, comp_return_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule shape_step_bind >>
  qexists `\y s. plain_operand s buf.buf_operand /\ plain_operand s y` >>
  reverse conj_tac
  >- (qspecl_then [`F`, `compiler_label`, `compiler_label`] irule shape_step_conseq >>
      irule_at Any shape_step_frame >> irule_at Any shape_step_emit_op_pre >>
      qexistsl [`\s. plain_operand s buf.buf_operand`,
        `\s. plain_operand s buf.buf_operand`] >>
      simp[SRULE [] (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands),
        plain_operand_def, lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
        inst_shape_ok_def, inst_jump_labels_ok_def, is_param_opcode_def,
        is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
        label_or_plain_def, is_label_operand_def]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[]
QED

Theorem alloc_run_slice_out_buf_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s)
    (compile_slice_out_buf out_size)
    (\v s. shape_state s /\ R s /\ EVERY (plain_operand s) [FST v; SND v])
Proof
  strip_tac >>
  ho_match_mp_tac (SRULE [] (Q.INST [`internal` |-> `F`, `P` |-> `\s. T`]
    alloc_run_fresh_shape_frame)) >>
  simp[alloc_run_compile_slice_out_buf, slice_out_buf_shape]
QED

Theory bodyPtrStructLitOwnershipScratchFrame
Ancestors bodyPtrStructLitOwnershipIfexpFrame bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  loweringShapeProps loweringShapeDefs loweringShapeRules compileEnv venomInst
  unitShapeDefs stackPlanTypes list

Theorem mstore_shape:
  shape_step F compiler_label (\s. EVERY (plain_operand s) [dst; src])
    (emit_void MSTORE [dst; src]) (\u s. T)
Proof
  irule shape_step_emit_void_pre >>
  simp[plain_operand_def, label_or_plain_def, lowered_inst_ok_def, mk_inst_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, is_label_operand_def]
QED

Theorem alloc_run_mstore_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ EVERY (plain_operand s) [dst; src])
    (emit_void MSTORE [dst; src]) (\u s. shape_state s /\ R s /\ T)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  simp[mstore_shape, alloc_run_emit_void_fresh]
QED

Theorem alloc_run_scratch_buffer_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s src)
    (comp_bind (compile_alloc_buffer n) (\b.
      comp_bind (emit_void MSTORE [b.buf_operand; src]) (\u.
        comp_return b.buf_operand)))
    (\p s. shape_state s /\ R s /\ plain_operand s p)
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\b s. shape_state s /\ (R s /\ plain_operand s src) /\
    plain_operand s b.buf_operand` >> reverse conj_tac
  >- (ho_match_mp_tac alloc_run_alloc_buffer_frame >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[src]` shape_stable_plain_operands)]) >>
  qx_gen_tac `buf` >> simp[] >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ (R s /\ plain_operand s buf.buf_operand) /\ T` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_mstore_frame >>
      qexists `\s. R s /\ plain_operand s buf.buf_operand` >>
      simp[shape_stable_conj,
        SRULE [] (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands)]) >>
  gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

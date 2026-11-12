Theory bodyPtrStructLitLoopShapeEmit
Ancestors loweringShapeProps loweringShapeRules loweringShapeDefs
  compileEnv venomInst unitShapeDefs stackPlanTypes list

Theorem loop_shape_op:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!s. R s ==> EVERY (plain_operand s) ops /\
    !id outs. lowered_inst_ok F (mk_inst id opc ops outs)) ==>
  shape_step F compiler_label R (emit_op opc ops)
    (\v s. R s /\ plain_operand s v)
Proof
  strip_tac >> irule shape_step_conseq >>
  irule_at Any shape_step_frame >> irule_at Any shape_step_emit_op_pre >>
  qexistsl [`R`, `R`] >> simp[] >> qexists `compiler_label` >>
  simp[] >> rpt strip_tac >> first_x_assum drule >>
  simp[EVERY_MEM, label_or_plain_def]
QED

Theorem loop_shape_void:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!s. R s ==> EVERY (plain_operand s) ops /\
    !id. lowered_inst_ok F (mk_inst id opc ops [])) ==>
  shape_step F compiler_label R (emit_void opc ops) (\u s. R s)
Proof
  strip_tac >> irule shape_step_conseq >>
  irule_at Any shape_step_frame >> irule_at Any shape_step_emit_void_pre >>
  qexistsl [`R`, `R`] >> simp[] >> qexists `compiler_label` >>
  simp[] >> rpt strip_tac >> first_x_assum drule >>
  simp[EVERY_MEM, label_or_plain_def]
QED

Theorem loop_shape_assign:
  shape_stable R /\
  (!s. R s ==> plain_operand s src /\ plain_operand s (Var dst)) ==>
  shape_step F compiler_label R (emit_inst ASSIGN [src] [dst]) (\u s. R s)
Proof
  strip_tac >> Cases_on `?s. R s`
  >- (pop_assum strip_assume_tac >>
      `~is_label_operand src` by
        (first_x_assum drule >> simp[plain_operand_def]) >>
      irule shape_step_conseq >> irule_at Any shape_step_emit_inst >>
      qexistsl [`R`, `compiler_label`] >>
      simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
        inst_shape_ok_def, inst_jump_labels_ok_def, is_param_opcode_def,
        is_read0_opcode_def, label_positions_ok_def, is_terminator_def] >>
      gvs[label_or_plain_def] >> metis_tac[]) >>
  gvs[shape_step_def]
QED

Theorem loop_shape_inst:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!s. R s ==> EVERY (label_or_plain s) ops /\
    EVERY (plain_operand s) (MAP Var outs) /\
    !id. lowered_inst_ok F (mk_inst id opc ops outs)) ==>
  shape_step F compiler_label R (emit_inst opc ops outs) (\u s. R s)
Proof
  strip_tac >> Cases_on `?s. R s`
  >- (pop_assum strip_assume_tac >>
      irule shape_step_conseq >> irule_at Any shape_step_emit_inst >>
      qexistsl [`R`, `compiler_label`] >> simp[] >>
      metis_tac[]) >>
  gvs[shape_step_def]
QED

Theorem loop_shape_jmp:
  shape_stable R /\ compiler_label lbl ==>
  shape_step F compiler_label R (emit_inst JMP [Label lbl] []) (\u s. R s)
Proof
  strip_tac >> irule loop_shape_inst >>
  simp[label_or_plain_def, is_label_operand_def, lowered_inst_ok_def,
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, jump_label_ok_def]
QED

Theorem loop_shape_jnz:
  shape_stable R /\ compiler_label yes /\ compiler_label no /\ yes <> no /\
  (!s. R s ==> plain_operand s test) ==>
  shape_step F compiler_label R
    (emit_inst JNZ [test; Label yes; Label no] []) (\u s. R s)
Proof
  strip_tac >> irule loop_shape_inst >>
  simp[label_or_plain_def, is_label_operand_def, lowered_inst_ok_def,
    mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, jump_label_ok_def] >>
  rpt strip_tac >> first_x_assum drule >>
  simp[plain_operand_def, is_label_operand_def] >>
  strip_tac >> gvs[is_label_operand_def]
QED

Theorem loop_extra_data_inst_ok:
  MEM opc [MUL; LT; EQ; ISZERO; SLOAD; TLOAD; SSTORE; TSTORE; ASSIGN; CALLDATALOAD] /\
  EVERY (plain_operand s) ops ==>
  ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  !id outs. lowered_inst_ok F (mk_inst id opc ops outs)
Proof
  strip_tac >>
  `EVERY (\op. ~is_label_operand op) ops` by
    (gvs[EVERY_MEM, plain_operand_def] >> metis_tac[]) >>
  qpat_x_assum `EVERY (plain_operand _) _` kall_tac >> gvs[MEM] >>
  gvs[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
    inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
    label_positions_ok_def, is_terminator_def]
QED

Theorem loop_shape_op_bind:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!s. R s ==> EVERY (plain_operand s) ops /\
    !id outs. lowered_inst_ok F (mk_inst id opc ops outs)) /\
  (!v. shape_step F compiler_label (\s. R s /\ plain_operand s v) (k v) Q) ==>
  shape_step F compiler_label R (comp_bind (emit_op opc ops) k) Q
Proof
  strip_tac >> irule shape_step_bind >>
  qexists `\v s. R s /\ plain_operand s v` >> simp[] >>
  irule loop_shape_op >> simp[] >> metis_tac[]
QED

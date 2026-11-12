Theory bodyPtrStructLitEmitterFrame
Ancestors bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps
  loweringShapeProps loweringShapeDefs loweringShapeRules compileEnv venomInst
  unitShapeDefs stackPlanTypes list

Theorem alloc_run_op_frame:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!s. R s /\ EVERY (plain_operand s) ops ==>
    !id outs. lowered_inst_ok F (mk_inst id opc ops outs)) ==>
  alloc_run (\s. shape_state s /\ R s /\ EVERY (plain_operand s) ops)
    (emit_op opc ops) (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  irule_at Any shape_step_emit_op_pre >> irule_at Any alloc_run_emit_op_fresh >>
  qexistsl [`R`, `\s. R s /\ EVERY (plain_operand s) ops`] >>
  simp[] >> rpt strip_tac >>
  gvs[EVERY_MEM, label_or_plain_def] >> metis_tac[]
QED

Theorem alloc_run_void_frame:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!s. R s /\ EVERY (plain_operand s) ops ==>
    !id. lowered_inst_ok F (mk_inst id opc ops [])) ==>
  alloc_run (\s. shape_state s /\ R s /\ EVERY (plain_operand s) ops)
    (emit_void opc ops) (\u s. shape_state s /\ R s)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  irule_at Any shape_step_emit_void_pre >> irule_at Any alloc_run_emit_void_fresh >>
  qexistsl [`R`, `\s. R s /\ EVERY (plain_operand s) ops`] >>
  simp[] >> rpt strip_tac >>
  gvs[EVERY_MEM, label_or_plain_def] >> metis_tac[]
QED

Theorem alloc_run_op_bind:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!s. R s ==> EVERY (plain_operand s) ops) /\
  (!s. R s ==> !id outs. lowered_inst_ok F (mk_inst id opc ops outs)) /\
  (!v. alloc_run (\s. shape_state s /\ R s /\ plain_operand s v) (k v) Q) ==>
  alloc_run (\s. shape_state s /\ R s) (comp_bind (emit_op opc ops) k) Q
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ R s /\ plain_operand s v` >> simp[] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_op_frame >>
  qexists `R` >> simp[] >> metis_tac[]
QED

Theorem alloc_run_void_bind:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!s. R s ==> EVERY (plain_operand s) ops) /\
  (!s. R s ==> !id. lowered_inst_ok F (mk_inst id opc ops [])) /\
  (!u. alloc_run (\s. shape_state s /\ R s) (k u) Q) ==>
  alloc_run (\s. shape_state s /\ R s) (comp_bind (emit_void opc ops) k) Q
Proof
  strip_tac >> irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ R s` >> simp[] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_void_frame >>
  qexists `R` >> simp[] >> metis_tac[]
QED

Theorem plain_data_inst_ok:
  MEM opc [ADD; MLOAD; SHL; EXTCODESIZE; SUB; SGT; MCOPY; MSTORE; ASSERT;
    CODECOPY; EXTCODECOPY] /\ EVERY (plain_operand s) ops ==>
  ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  !id outs. lowered_inst_ok F (mk_inst id opc ops outs)
Proof
  strip_tac >>
  `EVERY (\op. ~is_label_operand op) ops` by
    (gvs[EVERY_MEM, plain_operand_def] >> metis_tac[]) >>
  qpat_x_assum `EVERY (plain_operand _) _` kall_tac >> gvs[MEM] >>
  gvs[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
    inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
    label_positions_ok_def, is_terminator_def] >>
  rpt strip_tac >>
  namedCases_on `ops` ["", "a ts"] >> gvs[] >>
  namedCases_on `ts` ["", "b us"] >> gvs[] >>
  Cases_on `b` >> gvs[is_label_operand_def] >>
  namedCases_on `us` ["", "c vs"] >> gvs[] >>
  Cases_on `vs` >> gvs[] >> metis_tac[is_label_operand_def]
QED

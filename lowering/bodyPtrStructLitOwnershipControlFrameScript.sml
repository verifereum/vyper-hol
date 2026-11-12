Theory bodyPtrStructLitOwnershipControlFrame
Ancestors bodyPtrStructLitOwnershipIfexpFrame bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipStructFrame bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipShape loweringShapeRules loweringShapeDefs context compileEnv venomInst unitShapeDefs stackPlanTypes

Theorem alloc_run_fresh_label_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s) (fresh_label sfx)
    (\l s. shape_state s /\ R s /\ compiler_label l /\ label_sfx sfx l)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  irule_at Any shape_step_fresh_label_sfx >>
  simp[alloc_run_fresh_label_fresh] >> qexists `R` >> simp[] >> qexists `R` >> simp[]
QED

Theorem alloc_run_new_block_frame_checked[local]:
  shape_stable R /\ compiler_label l ==>
  alloc_run (\s. shape_state s /\ R s) (new_block l)
    (\v s. shape_state s /\ R s)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  irule_at Any shape_step_new_block >>
  simp[alloc_run_new_block_fresh] >> qexists `R` >> simp[] >> qexists `R` >> simp[]
QED

Theorem alloc_run_fresh_var_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s) fresh_var
    (\x s. shape_state s /\ R s /\ plain_operand s (Var x) /\
      not_fresh_at s x /\ ~alloc_owned s x)
Proof
  strip_tac >>
  `alloc_run (\s. shape_state s /\ R s) fresh_var
     (\x s. shape_state s /\ R s /\ plain_operand s (Var x))` by
    (irule alloc_run_conseq >>
     irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
     irule_at Any shape_step_fresh_var >>
     qexistsl [`R`, `R`] >> simp[] >>
     irule alloc_run_conseq >> irule_at Any alloc_run_fresh_var_fresh >> simp[]) >>
  fs[alloc_run_def] >> rpt strip_tac >>
  fs[shape_state_def] >> metis_tac[fresh_var_nonowned]
QED

Theorem alloc_run_emit_inst_frame:
  shape_stable R /\ opc <> ALLOCA /\
  ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!id. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
  alloc_run (\s. shape_state s /\ R s /\ EVERY (label_or_plain s) ops /\
    EVERY (plain_operand s) (MAP Var outs) /\
    EVERY (\x. ~alloc_owned s x) outs)
    (emit_inst opc ops outs) (\u s. shape_state s /\ R s)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any alloc_run_emit_inst >> simp[] >>
  irule_at Any shape_step_emit_inst >> simp[] >>
  qexistsl [`internal`, `R`] >> simp[]
QED

Theorem alloc_run_jnz_frame_checked[local]:
  shape_stable R /\ compiler_label l /\ compiler_label r /\ l <> r /\
  ~is_label_operand op ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s op)
    (emit_inst JNZ [op; Label l; Label r] [])
    (\u s. shape_state s /\ R s)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_emit_inst_frame) >>
  qexists `R` >>
  simp[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, label_positions_ok_def, is_terminator_def,
    is_read0_opcode_def, is_label_operand_def, jump_label_ok_def] >>
  metis_tac[is_label_operand_def]
QED

Theorem alloc_run_jmp_frame_checked[local]:
  shape_stable R /\ compiler_label l ==>
  alloc_run (\s. shape_state s /\ R s)
    (emit_inst JMP [Label l] []) (\u s. shape_state s /\ R s)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_emit_inst_frame) >>
  qexists `R` >>
  simp[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, label_positions_ok_def, is_terminator_def,
    is_read0_opcode_def, is_label_operand_def, jump_label_ok_def] >>
  metis_tac[is_label_operand_def]
QED

Theorem alloc_run_assign_frame_checked[local]:
  shape_stable R /\ ~is_label_operand op ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s op /\
    plain_operand s (Var x) /\ ~alloc_owned s x)
    (emit_inst ASSIGN [op] [x]) (\u s. shape_state s /\ R s)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_emit_inst_frame) >>
  qexists `R` >>
  simp[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, label_positions_ok_def, is_terminator_def,
    plain_operand_def, is_label_operand_def, is_read0_opcode_def]
QED

Theorem alloc_run_new_block_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ compiler_label l) (new_block l)
    (\u s. shape_state s /\ R s)
Proof
  simp[alloc_run_def] >>
  metis_tac[SRULE [alloc_run_def] alloc_run_new_block_frame_checked]
QED

Theorem alloc_run_jnz_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ compiler_label l /\ compiler_label r /\
    l <> r /\ ~is_label_operand op /\ plain_operand s op)
    (emit_inst JNZ [op; Label l; Label r] []) (\u s. shape_state s /\ R s)
Proof
  rw[alloc_run_def] >> drule_all alloc_run_jnz_frame_checked >>
  simp[alloc_run_def] >> disch_then drule_all >> simp[]
QED

Theorem alloc_run_jmp_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ compiler_label l)
    (emit_inst JMP [Label l] []) (\u s. shape_state s /\ R s)
Proof
  simp[alloc_run_def] >>
  metis_tac[SRULE [alloc_run_def] alloc_run_jmp_frame_checked]
QED

Theorem alloc_run_assign_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s op /\
    plain_operand s (Var x) /\ ~alloc_owned s x)
    (emit_inst ASSIGN [op] [x]) (\u s. shape_state s /\ R s)
Proof
  simp[alloc_run_def, plain_operand_def] >>
  metis_tac[SRULE [alloc_run_def, plain_operand_def] alloc_run_assign_frame_checked]
QED

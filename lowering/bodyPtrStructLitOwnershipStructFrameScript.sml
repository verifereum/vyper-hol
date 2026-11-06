Theory bodyPtrStructLitOwnershipStructFrame
Ancestors bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipConsumers
  bodyPtrStructLitOwnershipShape bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFreshness loweringShapeProps loweringShapeDefs
  loweringShapeRules exprLowering context compileEnv list venomInst unitShapeDefs stackPlanTypes

Theorem alloc_run_fresh_shape_frame:
  shape_step internal compiler_label P f Q /\ shape_stable R /\
  alloc_run fresh_outputs f (\v st. fresh_outputs st) ==>
  alloc_run (\st. shape_state st /\ R st /\ P st) f
    (\v st. shape_state st /\ R st /\ Q v st)
Proof
  strip_tac >> drule_all shape_step_frame >> strip_tac >>
  drule_all alloc_run_shape_join >> strip_tac >>
  irule alloc_run_conseq >> goal_assum (drule_at Any) >>
  simp[shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_unwrap_value_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ value_shape_ok s vv)
    (unwrap_value ce vv) (\v s. shape_state s /\ R s /\ plain_operand s v)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  simp[alloc_run_unwrap_value, unwrap_value_shape]
QED

Theorem alloc_run_store_memory_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s dst /\ plain_operand s src)
    (compile_store_memory ce src dst dt st)
    (\u s. shape_state s /\ R s /\ T)
Proof
  strip_tac >>
  ho_match_mp_tac (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  simp[alloc_run_compile_store_memory, compile_store_memory_shape]
QED

Theorem alloc_run_struct_address_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ plain_operand s buf)
    (emit_op ADD [buf; Lit (n2w off)])
    (\dst s. shape_state s /\ R s /\ plain_operand s dst)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  irule_at Any shape_step_emit_op_pre >>
  irule_at Any alloc_run_emit_op_fresh >>
  qexistsl [`R`, `\s. plain_operand s buf`] >>
  simp[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
       shape_stable_def, raw_opcode_ok_def, inst_shape_ok_def,
       inst_jump_labels_ok_def, is_param_opcode_def, plain_operand_def,
       is_label_operand_def, is_read0_opcode_def, label_positions_ok_def,
       is_terminator_def]
QED

Theorem alloc_run_struct_child_frame:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce) f
    (\v s. value_shape_ok s v) /\ shape_stable R /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) f (\v s. T) ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce) f
    (\v s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ value_shape_ok s v)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`LP` |-> `compiler_label`,
    `R` |-> `\s. R s /\ cenv_shape_ok s ce`] alloc_run_shape_frame) >>
  goal_assum (drule_at Any) >> qexistsl [`ce`, `R`, `\v s. T`] >>
  simp[shape_stable_conj, cenv_shape_ok_stable, SF ETA_ss]
QED

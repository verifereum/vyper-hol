Theory bodyPtrStructLitStmtSuffixFrame
Ancestors bodyPtrStructLitOwnershipStmtHelpers bodyPtrStructLitOwnershipFrame
  bodyPtrStructLitOwnershipSteps loweringShapeProps loweringShapeRules
  loweringShapeDefs context compileEnv stmtLowering venomInst
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipFreshness unitShapeDefs

Theorem alloc_run_compile_store_at_loc_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\
    plain_operand s dst /\ plain_operand s src)
    (compile_store_at_loc ce.ce_imm_alloca dst src loc)
    (\u s. shape_state s /\ R s /\ cenv_shape_ok s ce)
Proof
  strip_tac >>
  Cases_on `is_label_operand dst` >- simp[alloc_run_def, plain_operand_def] >>
  Cases_on `is_label_operand src` >- simp[alloc_run_def, plain_operand_def] >>
  Cases_on `loc = SOME LocCode`
  >- (gvs[compile_store_at_loc_def] >>
      irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `R`] alloc_run_shape_frame) >>
      irule_at Any compile_imm_store_word_shape >>
      irule_at Any alloc_run_conseq >>
      irule_at Any alloc_run_compile_imm_store_word >>
      simp[shape_state_def, shape_base_fresh_outputs] >>
      qexistsl [`R`, `\u s. T`] >> simp[]) >>
  Cases_on `loc` >> simp[compile_store_at_loc_def] >>
  TRY (rename1 `SOME l <> SOME LocCode` >> Cases_on `l` >>
       gvs[compile_store_at_loc_def]) >>
  (irule alloc_run_conseq >> irule_at Any alloc_run_shape_frame >>
   irule_at Any shape_step_emit_void >>
   irule_at Any alloc_run_conseq >>
   irule_at Any alloc_run_emit_void_fresh >>
   qexistsl [`F`, `\s. T`, `\s. R s /\ cenv_shape_ok s ce`, `\u s. T`] >>
   simp[shape_stable_conj, cenv_shape_ok_stable, shape_state_def,
     shape_base_fresh_outputs, label_or_plain_def, lowered_inst_ok_def,
     mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
     is_param_opcode_def, shape_stable_def, is_read0_opcode_def,
     label_positions_ok_def, is_terminator_def])
QED

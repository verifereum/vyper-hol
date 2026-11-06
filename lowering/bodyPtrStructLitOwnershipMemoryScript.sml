Theory bodyPtrStructLitOwnershipMemory
Ancestors bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipShape context compileEnv loweringShapeDefs
  loweringShapeRules loweringShapeProps emitHelper emitHelperProps
  unitShapeDefs venomInst stackPlanTypes list

Theorem alloc_run_compile_imm_load_word:
  alloc_run (\st. shape_base_state st /\ plain_operand st off /\
      (!base. imm = SOME base ==> plain_operand st base))
    (compile_imm_load_word is_ctor imm off) (\v st. T)
Proof
  reverse (Cases_on `is_ctor`)
  >- (simp[compile_imm_load_word_def] >> irule alloc_run_conseq >>
      irule_at Any (Q.INST [`opc` |-> `DLOAD`, `ops` |-> `[off]`]
        alloc_run_emit_op) >> simp[]) >>
  Cases_on `imm`
  >- (simp[compile_imm_load_word_def] >> irule alloc_run_conseq >>
      irule_at Any (Q.INST [`opc` |-> `ILOAD`, `ops` |-> `[off]`]
        alloc_run_emit_op) >> simp[]) >>
  rw[alloc_run_def, compile_imm_load_word_def, comp_bind_def] >>
  Cases_on `emit_op ADD [off; x] st` >> gvs[] >>
  `shape_base_state r` by
    (mp_tac (Q.SPECL [`F`, `compiler_label`, `ADD`, `[off; x]`, `st`, `q`, `r`]
       shape_base_emit_op) >>
     simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, inst_jump_labels_ok_def, is_terminator_def,
       is_read0_opcode_def, label_positions_ok_def,
       operand_case_not_label, is_param_opcode_def, label_or_plain_def] >>
     Cases_on `x` >> gvs[plain_operand_def, is_label_operand_def]) >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `ops` |-> `[off; x]`] alloc_run_emit_op) >>
  simp[alloc_run_def] >> disch_then drule_all >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `ILOAD`, `ops` |-> `[q]`] alloc_run_emit_op) >>
  simp[alloc_run_def] >> disch_then drule_all >> strip_tac >>
  metis_tac[alloc_frame_trans]
QED

Theorem alloc_run_compile_imm_store_word:
  alloc_run shape_base_state (compile_imm_store_word imm off v) (\u st. T)
Proof
  Cases_on `imm`
  >- (simp[compile_imm_store_word_def] >> irule alloc_run_conseq >>
      irule_at Any alloc_run_emit_void >> simp[]) >>
  rw[alloc_run_def, compile_imm_store_word_def, comp_bind_def] >>
  Cases_on `emit_op ADD [x; off] st` >> gvs[] >>
  mp_tac (Q.INST [`opc` |-> `ADD`, `ops` |-> `[x; off]`] alloc_run_emit_op) >>
  simp[alloc_run_def] >> disch_then drule_all >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `ISTORE`, `ops` |-> `[q; v]`] alloc_run_emit_void) >>
  simp[alloc_run_def] >> disch_then drule_all >> strip_tac >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  metis_tac[alloc_frame_trans]
QED

Theorem alloc_run_compile_ptr_load:
  !loc. alloc_run (\st. shape_base_state st /\ plain_operand st off /\
      (!base. imm = SOME base ==> plain_operand st base))
    (compile_ptr_load is_ctor imm loc off) (\v st. T)
Proof
  Cases >> simp[compile_ptr_load_def]
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_op >> simp[])
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_op >> simp[])
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_op >> simp[])
  >- irule alloc_run_compile_imm_load_word >>
  irule alloc_run_conseq >> irule_at Any alloc_run_emit_op >> simp[]
QED

Theorem alloc_run_compile_ptr_store:
  !loc. alloc_run shape_base_state
    (compile_ptr_store is_ctor imm loc dst v) (\u st. T)
Proof
  Cases >> simp[compile_ptr_store_def]
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_void >> simp[])
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_void >> simp[])
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_emit_void >> simp[])
  >- (Cases_on `is_ctor` >> simp[alloc_run_compile_imm_store_word] >>
      irule alloc_run_conseq >> irule_at Any alloc_run_emit_void >> simp[]) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_emit_void >> simp[]
QED

Theorem alloc_run_compile_copy_memory:
  !n. alloc_run (\st. T) (compile_copy_memory dst src n) (\u st. T)
Proof
  Cases >> simp[compile_copy_memory_def]
  >- simp[alloc_run_def, comp_return_def, alloc_frame_refl] >>
  irule alloc_run_emit_void
QED

Theorem alloc_run_compile_ptr_load_shape:
  alloc_run (\st. shape_state st /\
      cenv_shape_ok st ce /\ plain_operand st off)
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc off)
    (\v st. shape_state st /\ cenv_shape_ok st ce /\ plain_operand st v)
Proof
  irule alloc_run_conseq >>
  irule_at Any (Q.INST [`LP` |-> `compiler_label`] alloc_run_shape_join) >>
  irule_at Any compile_ptr_load_cenv_shape >>
  irule_at Any alloc_run_compile_ptr_load >>
  simp[shape_state_def, cenv_shape_ok_def] >> metis_tac[]
QED

Theorem alloc_run_compile_imm_store_word_shape:
  alloc_run (\st. shape_state st /\ cenv_shape_ok st ce /\
      plain_operand st off /\ plain_operand st v)
    (compile_imm_store_word ce.ce_imm_alloca off v)
    (\u st. shape_state st /\ cenv_shape_ok st ce)
Proof
  irule alloc_run_conseq >>
  irule_at Any (Q.INST [`LP` |-> `compiler_label`] alloc_run_shape_join) >>
  irule_at Any compile_imm_store_word_shape >>
  irule_at Any alloc_run_compile_imm_store_word >>
  simp[shape_state_def]
QED

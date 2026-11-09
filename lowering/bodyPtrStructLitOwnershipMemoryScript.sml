Theory bodyPtrStructLitOwnershipMemory
Ancestors bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipShape bodyPtrStructLitOwnershipFreshness
  context compileEnv loweringShapeDefs loweringShapeRules loweringShapeProps
  emitHelper emitHelperProps unitShapeDefs venomInst stackPlanTypes list

Theorem alloc_run_compile_imm_load_word:
  alloc_run fresh_outputs (compile_imm_load_word is_ctor imm off)
    (\v st. fresh_outputs st)
Proof
  Cases_on `is_ctor` >> Cases_on `imm` >>
  simp[compile_imm_load_word_def, comp_bind_def, alloc_run_emit_op_fresh] >>
  irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_imm_store_word:
  alloc_run fresh_outputs (compile_imm_store_word imm off v)
    (\u st. fresh_outputs st)
Proof
  Cases_on `imm` >>
  simp[compile_imm_store_word_def, comp_bind_def, alloc_run_emit_void_fresh] >>
  irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
       SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_ptr_load:
  !loc. alloc_run fresh_outputs (compile_ptr_load is_ctor imm loc off)
    (\v st. fresh_outputs st)
Proof
  Cases >> simp[compile_ptr_load_def, alloc_run_emit_op_fresh,
                alloc_run_compile_imm_load_word]
QED

Theorem alloc_run_compile_ptr_store:
  !loc. alloc_run fresh_outputs (compile_ptr_store is_ctor imm loc dst v)
    (\u st. fresh_outputs st)
Proof
  Cases >> simp[compile_ptr_store_def, alloc_run_emit_void_fresh] >>
  Cases_on `is_ctor` >>
  simp[alloc_run_compile_imm_store_word, alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_copy_memory:
  !n. alloc_run fresh_outputs (compile_copy_memory dst src n)
    (\u st. fresh_outputs st)
Proof
  Cases >> simp[compile_copy_memory_def, alloc_run_emit_void_fresh] >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl]
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
  simp[shape_state_def, shape_base_fresh_outputs]
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
  simp[shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_compile_with_byte_offset:
  alloc_run fresh_outputs (compile_with_byte_offset src_op off)
    (\v st. fresh_outputs st)
Proof
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, alloc_run_emit_op_fresh] >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_lit_byte_offset:
  alloc_run fresh_outputs (compile_lit_byte_offset src_op off)
    (\v st. fresh_outputs st)
Proof
  Cases_on `off = 0` >> Cases_on `src_op` >>
  simp[compile_lit_byte_offset_def, alloc_run_emit_op_fresh] >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_copy_memory_dynamic:
  alloc_run fresh_outputs (compile_copy_memory_dynamic dst src len)
    (\u st. fresh_outputs st)
Proof simp[compile_copy_memory_dynamic_def, alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_bytestring_copy_len:
  alloc_run fresh_outputs (compile_bytestring_copy_len src)
    (\v st. fresh_outputs st)
Proof
  simp[compile_bytestring_copy_len_def] >>
  irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  gen_tac >> irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  gen_tac >> irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_store_bytestring:
  alloc_run fresh_outputs (compile_store_bytestring src dst)
    (\u st. fresh_outputs st)
Proof
  simp[compile_store_bytestring_def] >>
  irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
       alloc_run_compile_bytestring_copy_len]
QED

Theorem alloc_run_frame_reserved:
  alloc_run P f Q ==>
  alloc_run (\st. P st /\ not_fresh_at st x /\ ~alloc_owned st x) f
    (\v st. Q v st /\ not_fresh_at st x /\ ~alloc_owned st x)
Proof rw[alloc_run_def, alloc_frame_def] >> metis_tac[]
QED

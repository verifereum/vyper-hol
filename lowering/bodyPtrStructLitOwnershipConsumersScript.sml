Theory bodyPtrStructLitOwnershipConsumers
Ancestors bodyPtrStructLitOwnershipTyped bodyPtrStructLitOwnershipLocations
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipShape
  context exprLowering compileEnv loweringShapeDefs loweringShapeRules
  loweringShapeProps

Theorem alloc_run_compile_store_memory:
  alloc_run fresh_outputs (compile_store_memory ce src dst dt st)
    (\u s. fresh_outputs s)
Proof
  Cases_on `is_word_type dt` >> Cases_on `is_bytestring_type dt` >>
  Cases_on `dt = st` >>
  simp[compile_store_memory_def, alloc_run_emit_void_fresh,
    alloc_run_compile_store_bytestring, alloc_run_compile_store_memory_typed,
    alloc_run_compile_copy_memory]
QED

Theorem alloc_run_unwrap_value:
  !vv. alloc_run fresh_outputs (unwrap_value ce vv) (\v s. fresh_outputs s)
Proof
  Cases >> simp[unwrap_value_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rename1 `is_word_type ty` >> Cases_on `is_word_type ty`
  >- simp[alloc_run_compile_ptr_load] >>
  Cases_on `p.ptr_location` >>
  simp[alloc_run_compile_ensure_in_memory] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_store_memory_shape:
  alloc_run (\s. shape_state s /\ plain_operand s dst /\ plain_operand s src)
    (compile_store_memory ce src dst dt st) (\u s. shape_state s)
Proof
  irule alloc_run_conseq >>
  irule_at Any (Q.INST [`LP` |-> `compiler_label`] alloc_run_shape_join) >>
  irule_at Any compile_store_memory_shape >>
  irule_at Any alloc_run_compile_store_memory >>
  simp[shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_unwrap_value_shape:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s vv)
    (unwrap_value ce vv) (\v s. shape_state s /\ plain_operand s v)
Proof
  irule alloc_run_conseq >>
  irule_at Any (Q.INST [`LP` |-> `compiler_label`] alloc_run_shape_join) >>
  irule_at Any unwrap_value_shape >>
  irule_at Any alloc_run_unwrap_value >>
  simp[shape_state_def, shape_base_fresh_outputs]
QED

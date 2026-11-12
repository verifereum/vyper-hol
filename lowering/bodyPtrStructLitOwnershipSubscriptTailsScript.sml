Theory bodyPtrStructLitOwnershipSubscriptTails
Ancestors bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps exprLowering compileEnv

Theorem alloc_run_compile_mapping_subscript:
  alloc_run fresh_outputs (compile_mapping_subscript slot key) (\v s. fresh_outputs s)
Proof
  simp[compile_mapping_subscript_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> rpt gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_keccak256_key:
  alloc_run fresh_outputs (compile_keccak256_key key is_bytes32) (\v s. fresh_outputs s)
Proof
  Cases_on `is_bytes32` >> simp[compile_keccak256_key_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> rpt gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_tuple_subscript:
  alloc_run fresh_outputs (compile_tuple_subscript base_op offset) (\v s. fresh_outputs s)
Proof
  simp[compile_tuple_subscript_def, SF ETA_ss,
    SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_array_subscript:
  (!p. alloc_run fresh_outputs (loader p) (\v s. fresh_outputs s)) ==>
  alloc_run fresh_outputs
    (compile_array_subscript base_op idx dyn static_count scale_n elem_bytes signed_idx loader)
    (\v s. fresh_outputs s)
Proof
  strip_tac >> Cases_on `dyn` >> Cases_on `signed_idx` >>
  simp[compile_array_subscript_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> rpt gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

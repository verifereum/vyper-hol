Theory bodyPtrStructLitOwnershipHashing
Ancestors bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps builtinHashing compileEnv

Theorem alloc_run_compile_keccak256_word:
  alloc_run fresh_outputs (compile_keccak256_word x) (\v s. fresh_outputs s)
Proof
  simp[compile_keccak256_word_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_keccak256_bytes:
  alloc_run fresh_outputs (compile_keccak256_bytes x) (\v s. fresh_outputs s)
Proof
  simp[compile_keccak256_bytes_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_keccak256_bytesm:
  alloc_run fresh_outputs (compile_keccak256_bytesm x m) (\v s. fresh_outputs s)
Proof
  simp[compile_keccak256_bytesm_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_sha256_word:
  alloc_run fresh_outputs (compile_sha256_word x) (\v s. fresh_outputs s)
Proof
  simp[compile_sha256_word_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_sha256_bytes:
  alloc_run fresh_outputs (compile_sha256_bytes x) (\v s. fresh_outputs s)
Proof
  simp[compile_sha256_bytes_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_sha256_bytesm:
  alloc_run fresh_outputs (compile_sha256_bytesm x m) (\v s. fresh_outputs s)
Proof
  simp[compile_sha256_bytesm_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

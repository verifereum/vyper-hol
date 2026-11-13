Theory bodyPtrStructLitOwnershipEC
Ancestors bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps builtinMisc compileEnv

Theorem alloc_run_compile_ecrecover:
  alloc_run fresh_outputs (compile_ecrecover h v r x) (\v s. fresh_outputs s)
Proof
  simp[compile_ecrecover_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_ecadd_points:
  alloc_run fresh_outputs (compile_ecadd_points p q) (\v s. fresh_outputs s)
Proof
  simp[compile_ecadd_points_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_ecmul_point:
  alloc_run fresh_outputs (compile_ecmul_point p x) (\v s. fresh_outputs s)
Proof
  simp[compile_ecmul_point_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

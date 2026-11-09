Theory bodyPtrStructLitOwnershipSliceTails
Ancestors bodyPtrStructLitOwnershipCalldataSlice
  bodyPtrStructLitOwnershipConvert bodyPtrStructLitOwnershipPrimitives
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps builtinBytes compileEnv

Theorem alloc_run_compile_slice_code:
  alloc_run fresh_outputs (compile_slice_code start len out_size) (\v s. T)
Proof
  simp[compile_slice_code_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[alloc_run_compile_slice_out_buf] >>
  Cases >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_assert_slice_bounds] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_slice_extcode:
  alloc_run fresh_outputs (compile_slice_extcode addr start len out_buf out_data) (\v s. T)
Proof
  simp[compile_slice_extcode_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_assert_slice_bounds] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_slice_data:
  alloc_run fresh_outputs (compile_slice_data src_len src_data start len out_size) (\v s. T)
Proof
  simp[compile_slice_data_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_compile_assert_slice_bounds] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

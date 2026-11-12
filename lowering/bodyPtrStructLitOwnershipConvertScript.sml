Theory bodyPtrStructLitOwnershipConvert
Ancestors bodyPtrStructLitOwnershipScalar bodyPtrStructLitOwnershipMemory
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipPrimitives exprLowering builtinBytes builtinSimple compileEnv pair

Theorem alloc_run_compile_int_clamp:
  alloc_run fresh_outputs (compile_int_clamp signed bits v) (\v s. fresh_outputs s)
Proof
  Cases_on `signed` >> simp[compile_int_clamp_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_load_bytestring_as_word:
  alloc_run fresh_outputs (load_bytestring_as_word v opc) (\v s. fresh_outputs s)
Proof
  simp[load_bytestring_as_word_def] >> Cases_on `opc = SAR` >>
  simp[comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_type_convert:
  !conv. alloc_run fresh_outputs (compile_type_convert v conv) (\v s. fresh_outputs s)
Proof
  Cases >> simp[compile_type_convert_def, comp_ignore_bind_def] >>
  rpt IF_CASES_TAC >> simp[comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_load_bytestring_as_word,
      SRULE [SF ETA_ss] alloc_run_compile_int_clamp] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
    simp[FORALL_PROD] >> rpt gen_tac >> simp[] >> rpt IF_CASES_TAC >> simp[]) >>
  rpt IF_CASES_TAC >> simp[] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
    SRULE [SF ETA_ss] alloc_run_compile_int_clamp] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_bytestring_widen_copy:
  alloc_run fresh_outputs (compile_bytestring_widen_copy dst v src)
    (\v s. fresh_outputs s)
Proof
  simp[compile_bytestring_widen_copy_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_compile_copy_memory] >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_zero_words:
  !n. alloc_run fresh_outputs (compile_zero_words base_op n) (\v s. fresh_outputs s)
Proof
  Induct >> simp[compile_zero_words_def, comp_ignore_bind_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_builtin_empty_complex:
  alloc_run fresh_outputs (compile_builtin_empty_complex nbytes bs)
    (\v s. fresh_outputs s)
Proof
  Cases_on `bs` >>
  simp[compile_builtin_empty_complex_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_compile_zero_words,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_bytestring_src:
  alloc_run fresh_outputs (compile_bytestring_src src) (\v s. fresh_outputs s)
Proof
  simp[compile_bytestring_src_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_assert_slice_bounds:
  alloc_run fresh_outputs (compile_assert_slice_bounds start len src)
    (\v s. fresh_outputs s)
Proof
  simp[compile_assert_slice_bounds_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_extract32_load:
  alloc_run fresh_outputs (compile_extract32_load len src start)
    (\v s. fresh_outputs s)
Proof
  simp[compile_extract32_load_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_assert_slice_bounds,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

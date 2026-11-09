Theory bodyPtrStructLitOwnershipLiterals
Ancestors bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps exprLowering context list pair compileEnv

Theorem alloc_run_compile_store_byte_chunks:
  !data_ptr bs offset.
  alloc_run fresh_outputs (compile_store_byte_chunks data_ptr bs offset)
    (\v s. fresh_outputs s)
Proof
  recInduct compile_store_byte_chunks_ind >> rpt strip_tac >>
  simp[Once compile_store_byte_chunks_def, comp_ignore_bind_def] >>
  TRY (simp[comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  simp[] >> rename1 `DROP 32 (h::t)` >>
  first_x_assum (qspecl_then [`TAKE 32 (h::t ++ REPLICATE 31 0w)`,
    `word_of_bytes T 0w (TAKE 32 (h::t ++ REPLICATE 31 0w))`] mp_tac) >> simp[SF ETA_ss]
QED

Theorem alloc_run_compile_bytelike_literal:
  alloc_run fresh_outputs (compile_bytelike_literal bytez max_len)
    (\v s. fresh_outputs s)
Proof
  simp[compile_bytelike_literal_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[alloc_run_compile_alloc_buffer] >>
  gen_tac >> simp[] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  gen_tac >> simp[] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_store_byte_chunks] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_literal_vv:
  alloc_run fresh_outputs (compile_literal_vv ty lit) (\v s. T)
Proof
  Cases_on `lit` >> simp[compile_literal_vv_def] >>
  TRY (rename1 `compile_literal_vv ty (BoolL b)` >> Cases_on `b` >>
    simp[compile_literal_vv_def, comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
  TRY (simp[comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
  rpt CASE_TAC >> simp[] >>
  TRY (simp[comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_bytelike_literal] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

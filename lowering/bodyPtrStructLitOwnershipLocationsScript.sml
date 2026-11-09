Theory bodyPtrStructLitOwnershipLocations
Ancestors bodyPtrStructLitOwnershipLoops bodyPtrStructLitOwnershipMemory
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipPrimitives
  bodyPtrStructLitOwnershipSteps context compileEnv venomInst list

Theorem alloc_run_compile_imm_copy_to_memory:
  !n off. alloc_run fresh_outputs
    (compile_imm_copy_to_memory is_ctor imm src dst n off)
    (\u st. fresh_outputs st)
Proof
  Induct
  >- simp[compile_imm_copy_to_memory_def, comp_return_def, alloc_run_def,
          alloc_frame_refl] >>
  gen_tac >> simp[compile_imm_copy_to_memory_def, comp_ignore_bind_def] >>
  ntac 4 (irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
    reverse conj_tac
    >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_lit_byte_offset,
      SRULE [SF ETA_ss] alloc_run_compile_imm_load_word,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh]) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  fs[SF ETA_ss]
QED

Theorem alloc_run_compile_imm_store_words:
  !n off. alloc_run fresh_outputs (compile_imm_store_words imm src dst n off)
    (\u st. fresh_outputs st)
Proof
  Induct
  >- simp[compile_imm_store_words_def, comp_return_def, alloc_run_def,
          alloc_frame_refl] >>
  gen_tac >> simp[compile_imm_store_words_def, comp_ignore_bind_def] >>
  ntac 4 (irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
    reverse conj_tac
    >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_lit_byte_offset,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_imm_store_word]) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  fs[SF ETA_ss]
QED

Theorem alloc_run_compile_store_immutable:
  alloc_run fresh_outputs (compile_store_immutable imm src dst words)
    (\u st. fresh_outputs st)
Proof simp[compile_store_immutable_def, alloc_run_compile_imm_store_words]
QED

Theorem alloc_run_compile_ensure_in_memory:
  !loc. alloc_run fresh_outputs
    (compile_ensure_in_memory ptr_op loc mem_bytes words is_ctor imm)
    (\v st. fresh_outputs st)
Proof
  Cases >> Cases_on `words = 1` >>
  simp[compile_ensure_in_memory_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
    reverse conj_tac
    >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_imm_copy_to_memory,
      SRULE [SF ETA_ss] alloc_run_compile_storage_to_memory,
      SRULE [SF ETA_ss] alloc_run_compile_transient_to_memory] >> NO_TAC) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[comp_return_def, comp_bind_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_load_storage:
  alloc_run fresh_outputs (compile_load_storage slot prim words mem_bytes)
    (\v st. fresh_outputs st)
Proof
  Cases_on `prim` >> Cases_on `words = 1` >>
  simp[compile_load_storage_def, comp_ignore_bind_def,
       alloc_run_emit_op_fresh] >>
  rpt (irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
    reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_storage_to_memory] >> NO_TAC) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_load_transient:
  alloc_run fresh_outputs (compile_load_transient slot prim words mem_bytes)
    (\v st. fresh_outputs st)
Proof
  Cases_on `prim` >> Cases_on `words = 1` >>
  simp[compile_load_transient_def, comp_ignore_bind_def,
       alloc_run_emit_op_fresh] >>
  rpt (irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
    reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_transient_to_memory] >> NO_TAC) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_load_calldata:
  alloc_run fresh_outputs (compile_load_calldata off prim words mem_bytes)
    (\v st. fresh_outputs st)
Proof
  Cases_on `prim` >> Cases_on `words = 1` >>
  simp[compile_load_calldata_def, comp_ignore_bind_def,
       alloc_run_emit_op_fresh] >>
  rpt (irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
    reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> NO_TAC) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_load_immutable:
  alloc_run fresh_outputs (compile_load_immutable off prim words mem_bytes is_ctor)
    (\v st. fresh_outputs st)
Proof
  Cases_on `prim` >> Cases_on `is_ctor` >>
  simp[compile_load_immutable_def, comp_ignore_bind_def,
       alloc_run_emit_op_fresh] >>
  rpt (irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
    reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_compile_code_to_memory] >> NO_TAC) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_load_memory:
  alloc_run fresh_outputs (compile_load_memory ptr_op prim)
    (\v st. fresh_outputs st)
Proof
  Cases_on `prim`
  >- simp[compile_load_memory_def, alloc_run_emit_op_fresh] >>
  simp[compile_load_memory_def, comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_store_storage:
  alloc_run fresh_outputs (compile_store_storage src slot prim words)
    (\u st. fresh_outputs st)
Proof
  Cases_on `prim` >> Cases_on `words = 1` >>
  simp[compile_store_storage_def, comp_ignore_bind_def,
       alloc_run_emit_void_fresh] >>
  irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
         SRULE [SF ETA_ss] alloc_run_compile_memory_to_storage] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
       SRULE [SF ETA_ss] alloc_run_compile_memory_to_storage,
       SRULE [SF ETA_ss] alloc_run_compile_memory_to_transient] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_store_transient:
  alloc_run fresh_outputs (compile_store_transient src slot prim words)
    (\u st. fresh_outputs st)
Proof
  Cases_on `prim` >> Cases_on `words = 1` >>
  simp[compile_store_transient_def, comp_ignore_bind_def,
       alloc_run_emit_void_fresh] >>
  irule alloc_run_bind >> qexists `\v st. fresh_outputs st` >>
  reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
         SRULE [SF ETA_ss] alloc_run_compile_memory_to_transient] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
       SRULE [SF ETA_ss] alloc_run_compile_memory_to_storage,
       SRULE [SF ETA_ss] alloc_run_compile_memory_to_transient] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

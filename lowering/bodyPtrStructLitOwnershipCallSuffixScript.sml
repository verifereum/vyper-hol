Theory bodyPtrStructLitOwnershipCallSuffix
Ancestors bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipScalar
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps builtinSystem builtinCreate context compileEnv

Theorem alloc_run_compile_msg_data_to_memory:
  alloc_run fresh_outputs compile_msg_data_to_memory (\v s. fresh_outputs s)
Proof
  simp[compile_msg_data_to_memory_def, compile_alloc_dynamic_def,
       comp_ignore_bind_def] >>
  ntac 3 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
    gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_raw_call_outbuf:
  alloc_run fresh_outputs (compile_raw_call_outbuf n) (\v s. fresh_outputs s)
Proof
  simp[compile_raw_call_outbuf_def] >> IF_CASES_TAC >> simp[] >>
  (rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
            SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
        simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
    gen_tac >> simp[]) >>
   simp[comp_return_def, alloc_run_def, alloc_frame_refl])
QED

Theorem alloc_run_compile_check_create_result:
  alloc_run fresh_outputs (compile_check_create_result result rev)
    (\v s. fresh_outputs s)
Proof
  Cases_on `rev` >> simp[compile_check_create_result_def, comp_ignore_bind_def] >>
  TRY (simp[comp_return_def, alloc_run_def, alloc_frame_refl] >> NO_TAC) >>
  ntac 9 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
        SRULE [SF ETA_ss, listTheory.EVERY_DEF]
          (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh),
        SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
        SRULE [SF ETA_ss] alloc_run_new_block_fresh] >>
    gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_create_dispatch:
  alloc_run fresh_outputs (compile_create_dispatch codeptr len value salt rev)
    (\v s. fresh_outputs s)
Proof
  simp[compile_create_dispatch_def] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (Cases_on `salt` >>
      simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_check_create_result]
QED

Theorem alloc_run_compile_create_proxy_buf:
  alloc_run fresh_outputs (compile_create_proxy_buf target) (\v s. fresh_outputs s)
Proof
  simp[compile_create_proxy_buf_def, comp_ignore_bind_def] >>
  ntac 8 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
        simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
    gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_create_blueprint_check:
  alloc_run fresh_outputs (compile_create_blueprint_check target off)
    (\v s. fresh_outputs s)
Proof
  simp[compile_create_blueprint_check_def, comp_ignore_bind_def] >>
  ntac 4 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
    gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_create_copy:
  alloc_run fresh_outputs (compile_create_copy target value salt rev)
    (\v s. fresh_outputs s)
Proof
  Cases_on `salt` >> Cases_on `rev` >>
  simp[compile_create_copy_def, compile_alloc_dynamic_def, comp_ignore_bind_def] >>
  (rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (simp[SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
        simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
    gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_check_create_result])
QED

Theorem alloc_run_compile_create_blueprint_append:
  alloc_run fresh_outputs
    (compile_create_blueprint_append target value salt off codesz args arglen rev)
    (\v s. fresh_outputs s)
Proof
  Cases_on `salt` >> Cases_on `rev` >> Cases_on `arglen = Lit 0w` >>
  simp[compile_create_blueprint_append_def, compile_alloc_dynamic_def,
       comp_ignore_bind_def, comp_bind_assoc] >>
  (rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (simp[SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
        SRULE [SF ETA_ss] alloc_run_compile_copy_memory_dynamic] >>
        simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
    gen_tac >> simp[]) >>
   simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_check_create_result])
QED

Theorem alloc_run_compile_raw_call_finish:
  alloc_run fresh_outputs
    (compile_raw_call_finish to_op data_ptr data_len gas value callty n rev outval outptr)
    (\v s. fresh_outputs s)
Proof
  Cases_on `callty` >> Cases_on `rev` >> Cases_on `0 < n` >>
  simp[compile_raw_call_finish_def, comp_ignore_bind_def] >>
  (rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss,
        SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
        SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
        SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
        SRULE [SF ETA_ss] alloc_run_compile_select,
        SRULE [SF ETA_ss, listTheory.EVERY_DEF]
          (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh),
        SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
        SRULE [SF ETA_ss] alloc_run_new_block_fresh] >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
   simp[comp_return_def, alloc_run_def, alloc_frame_refl])
QED

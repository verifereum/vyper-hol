Theory bodyPtrStructLitOwnershipAbiEncode
Ancestors bodyPtrStructLitOwnershipAbiStatic bodyPtrStructLitOwnershipPrimitives
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps abiEncoder context compileEnv

Theorem alloc_run_compile_abi_encode_dyn_static_loop:
  alloc_run fresh_outputs
    (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
    (\r s. fresh_outputs s)
Proof
  simp[compile_abi_encode_dyn_static_loop_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
      SRULE [SF ETA_ss] alloc_run_new_block_fresh,
      SRULE [SF ETA_ss, listTheory.EVERY_DEF]
        (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh),
      SRULE [SF ETA_ss] alloc_run_compile_abi_encode_static_info] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_abi_encode_mutual:
  (!dst cp ci dyn off dp. alloc_run fresh_outputs
    (compile_abi_encode_child dst cp ci dyn off dp) (\r s. fresh_outputs s)) /\
  (!dst src info. alloc_run fresh_outputs
    (compile_abi_encode_to_buf dst src info) (\r s. fresh_outputs s)) /\
  (!dst src es so ho dp. alloc_run fresh_outputs
    (compile_abi_encode_complex_elems dst src es so ho dp) (\r s. fresh_outputs s)) /\
  (!dst src ei asz msz len. alloc_run fresh_outputs
    (compile_abi_encode_dyn_loop dst src ei asz msz len) (\r s. fresh_outputs s))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac
  >- suspend "child"
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "copy"
  >- suspend "array"
  >- suspend "empty_complex"
  >- suspend "complex"
  >- suspend "empty_elems"
  >- suspend "elems"
  >> suspend "loop"
QED

Resume alloc_run_abi_encode_mutual[word]:
  simp[compile_abi_encode_child_def, alloc_run_compile_abi_encode_static]
QED
Resume alloc_run_abi_encode_mutual[empty_complex]:
  simp[compile_abi_encode_child_def, comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Resume alloc_run_abi_encode_mutual[empty_elems]:
  simp[compile_abi_encode_child_def, comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Resume alloc_run_abi_encode_mutual[copy]:
  rpt gen_tac >> simp[compile_abi_encode_child_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Resume alloc_run_abi_encode_mutual[bytes]:
  rpt gen_tac >> simp[compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED
Resume alloc_run_abi_encode_mutual[child]:
  rpt gen_tac >> Cases_on `dyn` >> simp[] >> strip_tac >>
  rule_assum_tac (SRULE [SF ETA_ss]) >>
  simp[compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Resume alloc_run_abi_encode_mutual[elems]:
  rpt gen_tac >> strip_tac >> rule_assum_tac (SRULE [SF ETA_ss]) >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  gvs[SF ETA_ss, arithmeticTheory.ADD_COMM]
QED
Resume alloc_run_abi_encode_mutual[array]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer] >>
  gen_tac >> simp[] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  Cases_on `elem_is_dyn` >> gvs[SF ETA_ss] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_abi_encode_dyn_static_loop,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Resume alloc_run_abi_encode_mutual[complex]:
  rpt gen_tac >> strip_tac >> gvs[SF ETA_ss] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> gvs[SF ETA_ss] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Resume alloc_run_abi_encode_mutual[loop]:
  rpt gen_tac >> strip_tac >> gvs[SF ETA_ss] >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
      SRULE [SF ETA_ss] alloc_run_new_block_fresh,
      SRULE [SF ETA_ss, listTheory.EVERY_DEF]
        (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh)] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED
Finalise alloc_run_abi_encode_mutual

Theorem alloc_run_compile_abi_encode_child:
  alloc_run fresh_outputs (compile_abi_encode_child dst child_ptr ci dyn off dp)
    (\r s. fresh_outputs s)
Proof
  simp[alloc_run_abi_encode_mutual]
QED
Theorem alloc_run_compile_abi_encode_to_buf:
  alloc_run fresh_outputs (compile_abi_encode_to_buf dst src info)
    (\r s. fresh_outputs s)
Proof
  simp[alloc_run_abi_encode_mutual]
QED
Theorem alloc_run_compile_abi_encode_complex_elems:
  alloc_run fresh_outputs (compile_abi_encode_complex_elems dst src es so ho dp)
    (\r s. fresh_outputs s)
Proof
  simp[alloc_run_abi_encode_mutual]
QED
Theorem alloc_run_compile_abi_encode_dyn_loop:
  alloc_run fresh_outputs (compile_abi_encode_dyn_loop dst src ei asz msz len)
    (\r s. fresh_outputs s)
Proof
  simp[alloc_run_abi_encode_mutual]
QED

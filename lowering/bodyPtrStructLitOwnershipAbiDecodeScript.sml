Theory bodyPtrStructLitOwnershipAbiDecode
Ancestors bodyPtrStructLitOwnershipAbiStatic bodyPtrStructLitOwnershipPrimitives
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps abiEncoder
  context compileEnv

Theorem alloc_run_compile_abi_dec_addr:
  alloc_run fresh_outputs (compile_abi_dec_addr base_op p)
    (\r s. fresh_outputs s)
Proof
  Cases_on `base_op = Lit 0w` >> simp[compile_abi_dec_addr_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_abi_decode_range_check:
  alloc_run fresh_outputs (compile_abi_decode_range_check lo hi_end hi)
    (\r s. fresh_outputs s)
Proof
  simp[compile_abi_decode_range_check_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_getelemptr_abi:
  alloc_run fresh_outputs (compile_getelemptr_abi src dyn off opc base_op hi)
    (\r s. fresh_outputs s)
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >>
  simp[compile_getelemptr_abi_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_abi_dec_addr,
      SRULE [SF ETA_ss] alloc_run_compile_abi_decode_range_check] >> gen_tac >> simp[]) >>
  simp[comp_bind_def, comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_abi_decode_dyn_elem_ptr:
  alloc_run fresh_outputs (compile_abi_decode_dyn_elem_ptr opc base_op src data hi asz)
    (\r s. fresh_outputs s)
Proof
  Cases_on `hi = Lit 0w` >>
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_abi_dec_addr,
      SRULE [SF ETA_ss] alloc_run_compile_abi_decode_range_check] >> gen_tac >> simp[]) >>
  simp[comp_bind_def, comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_abi_decode_mutual:
  (!dst src opc base_op hi info. alloc_run fresh_outputs
    (compile_abi_decode_to_buf dst src opc base_op hi info) (\r s. fresh_outputs s)) /\
  (!dst src opc base_op hi es ao vo. alloc_run fresh_outputs
    (compile_abi_decode_complex_elems dst src opc base_op hi es ao vo) (\r s. fresh_outputs s)) /\
  (!dst src opc base_op hi ei asz msz ip cnt. alloc_run fresh_outputs
    (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt) (\r s. fresh_outputs s))
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "empty"
  >- suspend "elems"
  >> suspend "loop"
QED
Resume alloc_run_abi_decode_mutual[word]:
  simp[Once compile_abi_decode_to_buf_def] >> rpt gen_tac >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_abi_dec_addr] >>
  gen_tac >> simp[SF ETA_ss] >>
  irule (SRULE [SF ETA_ss] alloc_run_compile_abi_decode_static) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_abi_clamp_basetype]
QED
Resume alloc_run_abi_decode_mutual[empty]:
  simp[Once compile_abi_decode_to_buf_def, comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Resume alloc_run_abi_decode_mutual[complex]:
  rpt gen_tac >> Cases_on `hi = Lit 0w` >> simp[] >> strip_tac >>
  gvs[SF ETA_ss] >> simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_abi_dec_addr,
      SRULE [SF ETA_ss] alloc_run_compile_abi_decode_range_check] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss]
QED
Resume alloc_run_abi_decode_mutual[elems]:
  rpt gen_tac >> strip_tac >> gvs[SF ETA_ss] >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_getelemptr_abi] >> gen_tac >> simp[]) >>
  gvs[SF ETA_ss, arithmeticTheory.ADD_COMM]
QED
Resume alloc_run_abi_decode_mutual[bytes]:
  rpt gen_tac >> Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_abi_dec_addr,
      SRULE [SF ETA_ss] alloc_run_compile_abi_decode_range_check, comp_return_def] >>
      simp[alloc_run_def, comp_return_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_abi_dec_addr,
      SRULE [SF ETA_ss] alloc_run_compile_abi_decode_range_check]
QED

Resume alloc_run_abi_decode_mutual[array]:
  rpt gen_tac >> strip_tac >>
  Cases_on `hi = Lit 0w` >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_abi_dec_addr,
      SRULE [SF ETA_ss] alloc_run_compile_abi_decode_range_check] >>
      simp[alloc_run_def, comp_return_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp ei` >> gvs[SF ETA_ss] >>
  simp[comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer] >> gen_tac >> simp[]) >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_abi_dec_addr,
      SRULE [SF ETA_ss] alloc_run_compile_abi_decode_range_check]
QED
Resume alloc_run_abi_decode_mutual[loop]:
  rpt gen_tac >> strip_tac >> gvs[SF ETA_ss] >>
  Cases_on `dec_info_needs_offset ei` >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_abi_decode_dyn_elem_ptr,
      SRULE [SF ETA_ss] alloc_run_compile_abi_dec_addr,
      SRULE [SF ETA_ss] alloc_run_fresh_label_fresh,
      SRULE [SF ETA_ss] alloc_run_new_block_fresh,
      SRULE [SF ETA_ss, listTheory.EVERY_DEF]
        (Q.INST [`outs` |-> `[]`] alloc_run_emit_inst_fresh)] >>
      simp[alloc_run_def, comp_return_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[alloc_run_def, comp_return_def, alloc_frame_refl]
QED
Finalise alloc_run_abi_decode_mutual

Theorem alloc_run_compile_abi_decode_to_buf:
  alloc_run fresh_outputs (compile_abi_decode_to_buf dst src opc base_op hi info)
    (\r s. fresh_outputs s)
Proof
  simp[alloc_run_abi_decode_mutual]
QED

Theorem alloc_run_compile_abi_decode_complex_elems:
  alloc_run fresh_outputs (compile_abi_decode_complex_elems dst src opc base_op hi es ao vo)
    (\r s. fresh_outputs s)
Proof
  simp[alloc_run_abi_decode_mutual]
QED

Theorem alloc_run_compile_abi_decode_dyn_loop:
  alloc_run fresh_outputs (compile_abi_decode_dyn_loop dst src opc base_op hi ei asz msz ip cnt)
    (\r s. fresh_outputs s)
Proof
  simp[alloc_run_abi_decode_mutual]
QED

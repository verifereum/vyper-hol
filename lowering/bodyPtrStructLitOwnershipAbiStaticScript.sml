Theory bodyPtrStructLitOwnershipAbiStatic
Ancestors bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipConsumers bodyPtrStructLitOwnershipMemory
  abiEncoder exprLowering context compileEnv

Theorem alloc_run_compile_abi_int_clamp:
  alloc_run fresh_outputs (compile_abi_int_clamp v bits signed_idx)
    (\r s. fresh_outputs s)
Proof
  simp[compile_abi_int_clamp_def] >> Cases_on `signed_idx` >> simp[] >> (
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
    SRULE [SF ETA_ss] alloc_run_emit_void_fresh])
QED

Theorem alloc_run_compile_abi_bytes_clamp:
  alloc_run fresh_outputs (compile_abi_bytes_clamp v m) (\r s. fresh_outputs s)
Proof
  simp[compile_abi_bytes_clamp_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
    SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_abi_clamp_basetype:
  !cl. alloc_run fresh_outputs (compile_abi_clamp_basetype v cl) (\r s. fresh_outputs s)
Proof
  Cases >> simp[compile_abi_clamp_basetype_def, alloc_run_compile_abi_int_clamp,
    alloc_run_compile_abi_bytes_clamp]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
    SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_abi_zero_pad:
  alloc_run fresh_outputs (compile_abi_zero_pad ptr_op len count_op) (\r s. fresh_outputs s)
Proof
  simp[compile_abi_zero_pad_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh]
QED

Theorem alloc_run_compile_get_element_ptr:
  alloc_run fresh_outputs (compile_get_element_ptr ptr_op off) (\r s. fresh_outputs s)
Proof
  simp[compile_get_element_ptr_def, alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_get_dynarray_elem_ptr:
  alloc_run fresh_outputs (compile_get_dynarray_elem_ptr ptr_op idx sz) (\r s. fresh_outputs s)
Proof
  simp[compile_get_dynarray_elem_ptr_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_abi_encode_static:
  alloc_run fresh_outputs (compile_abi_encode_static dst src) (\r s. fresh_outputs s)
Proof
  simp[compile_abi_encode_static_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_abi_decode_static:
  (!v. alloc_run fresh_outputs (clamp_fn v) (\u s. fresh_outputs s)) ==>
  alloc_run fresh_outputs (compile_abi_decode_static src dst opc clamp_fn)
    (\r s. fresh_outputs s)
Proof
  strip_tac >> simp[compile_abi_decode_static_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  first_x_assum (mp_tac o SRULE [SF ETA_ss]) >> simp[]
QED

Theorem alloc_run_compile_abi_encode_static_info:
  !info. alloc_run fresh_outputs (compile_abi_encode_static_info dst src info)
    (\r s. fresh_outputs s)
Proof
  Cases >> simp[compile_abi_encode_static_info_def, alloc_run_compile_abi_encode_static,
    comp_ignore_bind_def]
  >~ [`alloc_run _ (comp_bind _ _) _`]
  >- (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
      >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_compile_store_abi_tuple:
  !vs buf off. alloc_run fresh_outputs (compile_store_abi_tuple ce buf off vs)
    (\r s. fresh_outputs s)
Proof
  Induct >> simp[compile_store_abi_tuple_def]
  >- simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rpt gen_tac >> PairCases_on `h` >> simp[compile_store_abi_tuple_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
        SRULE [SF ETA_ss] alloc_run_compile_copy_memory]) >>
  simp[SF ETA_ss] >> first_x_assum (mp_tac o SRULE [SF ETA_ss]) >> simp[]
QED

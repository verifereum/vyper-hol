Theory bodyPtrStructLitOwnershipAbiWrappers
Ancestors bodyPtrStructLitOwnershipAbiEncode bodyPtrStructLitOwnershipAbiDecode
  bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps builtinAbi context compileEnv

Theorem alloc_run_lower_abi_encode:
  alloc_run fresh_outputs (lower_abi_encode ensure mid src info maxlen)
    (\r s. fresh_outputs s)
Proof
  Cases_on `mid` >>
  simp[lower_abi_encode_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_compile_abi_encode_to_buf] >>
      simp[alloc_run_def, comp_return_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[comp_bind_def, alloc_run_def, comp_return_def, alloc_frame_refl]
QED

Theorem alloc_run_lower_abi_decode:
  alloc_run fresh_outputs (lower_abi_decode data info amin amax outsz)
    (\r s. fresh_outputs s)
Proof
  Cases_on `amin = amax` >>
  simp[lower_abi_decode_def, comp_ignore_bind_def, comp_bind_assoc] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
    >- (simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_compile_abi_decode_to_buf] >>
      simp[alloc_run_def, comp_return_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[comp_bind_def, alloc_run_def, comp_return_def, alloc_frame_refl]
QED

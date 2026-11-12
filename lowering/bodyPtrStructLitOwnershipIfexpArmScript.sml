Theory bodyPtrStructLitOwnershipIfexpArm
Ancestors bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipConsumers
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipFreshness
  exprLowering context compileEnv

Theorem alloc_run_compile_ifexp_arm:
  alloc_run fresh_outputs (compile_ifexp_arm ce rt at vv) (\v s. fresh_outputs s)
Proof
  rw[compile_ifexp_arm_def] >> simp[alloc_run_unwrap_value] >>
  simp[comp_ignore_bind_def] >>
  ntac 3 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
            SRULE [SF ETA_ss] alloc_run_unwrap_value,
            SRULE [SF ETA_ss] alloc_run_compile_store_memory] >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

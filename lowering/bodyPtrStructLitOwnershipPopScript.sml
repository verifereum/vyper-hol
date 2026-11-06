Theory bodyPtrStructLitOwnershipPop
Ancestors bodyPtrStructLitOwnershipSubscriptTails bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps loweringShapeProps loweringShapeDefs
  exprLowering compileEnv context

Theorem alloc_run_compile_dynarray_pop:
  alloc_run fresh_outputs (compile_dynarray_pop base_op ws sz ctor imm loc)
    (\v s. fresh_outputs s)
Proof
  simp[compile_dynarray_pop_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_ptr_load,
      SRULE [SF ETA_ss] alloc_run_compile_ptr_store,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> rpt gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

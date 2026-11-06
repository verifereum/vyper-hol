Theory bodyPtrStructLitOwnershipStructLoop
Ancestors bodyPtrStructLitOwnershipConsumers bodyPtrStructLitOwnershipMemory
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  exprLowering context compileEnv list

Theorem alloc_run_compile_struct_lit:
  !fields ty buf off.
  (!fname e. MEM (fname,e) fields ==>
    alloc_run fresh_outputs (cfn ce (expr_type e) e) (\vv s. fresh_outputs s)) ==>
  alloc_run fresh_outputs (compile_struct_lit cfn ce ty fields buf off)
    (\op s. fresh_outputs s)
Proof
  Induct
  >- simp[compile_struct_lit_def, comp_return_def, alloc_run_def,
          alloc_frame_refl] >>
  qx_gen_tac `head` >> PairCases_on `head` >> rpt gen_tac >> strip_tac >>
  simp[compile_struct_lit_def, comp_ignore_bind_def] >>
  ntac 4 (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac
    >- (fs[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
       SRULE [SF ETA_ss] alloc_run_unwrap_value,
       SRULE [SF ETA_ss] alloc_run_compile_store_memory] >>
       first_x_assum irule >> simp[]) >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  fs[SF ETA_ss] >> first_x_assum irule >> rpt strip_tac >>
  first_x_assum irule >> qexists `fname` >> simp[]
QED

Theory bodyPtrStructLitOwnershipMethodId
Ancestors bodyPtrStructLitOwnershipHashing bodyPtrStructLitOwnershipPrimitives
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipLiterals bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipSliceCases loweringShapeDefs loweringShapeRules
  loweringShapeProps builtinHashing exprLowering compileEnv context list pair
  gasShadowCompileBase

Theorem alloc_run_compile_method_id_hash:
  alloc_run fresh_outputs (compile_method_id_hash arg_ty val_op)
    (\v s. fresh_outputs s)
Proof
  simp[oneline compile_method_id_hash_def] >> rpt CASE_TAC >>
  simp[alloc_run_compile_keccak256_bytesm, alloc_run_compile_keccak256_bytes]
QED

Theorem alloc_run_compile_method_id_runtime:
  alloc_run fresh_outputs (compile_method_id_runtime arg_ty val_op is_bytes4)
    (\v s. T)
Proof
  Cases_on `is_bytes4` >>
  simp[compile_method_id_runtime_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- (simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_method_id_hash,
      SRULE [SF ETA_ss] alloc_run_compile_alloc_buffer,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >> gen_tac >> simp[]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_builtin_method_id:
  1 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty MethodId args) (\v s. T)
Proof
  strip_tac >> `MEM (HD args) args` by (Cases_on `args` >> gvs[]) >>
  Cases_on `method_id_literal (HD args)`
  >- (GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
    simp[compile_builtin_dispatch_body_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
    irule alloc_run_lower_value_then >> reverse conj_tac >- metis_tac[] >>
    gen_tac >> simp[alloc_run_def, oneline as_stack_val_def,
      oneline as_ptr_val_def, AllCaseEqs()] >>
    rpt strip_tac >> gvs[] >> rename1 `shape_state last` >>
    `fresh_outputs last` by metis_tac[shape_state_def, shape_base_fresh_outputs] >>
    metis_tac[SRULE [alloc_run_def] alloc_run_compile_method_id_runtime]) >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def] >> simp[SF ETA_ss] >>
  irule alloc_run_conseq >> irule_at Any alloc_run_compile_literal_vv >>
  simp[] >> metis_tac[shape_state_def, shape_base_fresh_outputs]
QED

Theory bodyPtrStructLitOwnershipEnvironmentCases
Ancestors bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipInterfaces bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps exprLowering builtinSimple loweringShapeDefs
  loweringShapeRules loweringShapeProps compileEnv context list pair

Theorem alloc_run_compile_env_var:
  alloc_run fresh_outputs (compile_env_var item) (\v s. fresh_outputs s)
Proof
  Cases_on `item` >> simp[compile_env_var_def, alloc_run_emit_op_fresh] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >> gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem alloc_run_compile_builtin_len:
  alloc_run fresh_outputs (compile_builtin_len ctor imm op loc)
    (\v s. fresh_outputs s)
Proof
  simp[compile_builtin_len_def, alloc_run_compile_ptr_load]
QED

Theorem alloc_run_builtin_env:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty (Env item) args) (\v s. T)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def] >> simp[SF ETA_ss] >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[SRULE [alloc_run_def] alloc_run_compile_env_var,
    shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_builtin_calldata_len:
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty CalldataLen args) (\v s. T)
Proof
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, compile_builtin_calldatasize_def] >>
  simp[SF ETA_ss] >>
  simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[SRULE [alloc_run_def] alloc_run_emit_op_fresh,
    shape_state_def, shape_base_fresh_outputs]
QED

Theorem alloc_run_builtin_len:
  1 <= LENGTH args /\
  (!e t. MEM e args ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (cfn ce t e) (\v s. value_shape_ok s v) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (cfn ce t e) (\v s. T)) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_builtin_dispatch_body cfn ce rt ty Len args) (\v s. T)
Proof
  strip_tac >> `MEM (HD args) args` by (Cases_on `args` >> gvs[]) >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_builtin_dispatch_body_def, comp_bind_uncurry] >> simp[SF ETA_ss] >>
  irule alloc_run_bind >>
  qexists `\v s. shape_state s /\ cenv_shape_ok s ce /\ value_shape_ok s v` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_struct_child_frame >>
      qexistsl [`internal`, `ce`, `\s. T`] >>
      simp[shape_stable_def] >> metis_tac[]) >>
  gen_tac >> simp[alloc_run_def, oneline as_stack_val_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[SRULE [alloc_run_def] alloc_run_compile_builtin_len,
    shape_state_def, shape_base_fresh_outputs]
QED

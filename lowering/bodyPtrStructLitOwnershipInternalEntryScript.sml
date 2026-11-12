Theory bodyPtrStructLitOwnershipInternalEntry
Ancestors
  bodyPtrStructLitOwnershipInternalShape bodyPtrStructLitOwnershipModuleParams
  bodyPtrStructLitOwnershipShape bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps loweringShapeDefs loweringShapeProps
  compileEnv

Theorem alloc_run_internal_param_capture:
  !params idx. alloc_run shape_state (compile_internal_param_decls params idx)
    (\r st. shape_state st /\
      EVERY (\(name,is_stack,op). plain_operand st op) (FST r) /\
      fresh_outputs st)
Proof
  rpt gen_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any structlit_compile_internal_param_decls_shape >>
  irule_at Any alloc_run_compile_internal_param_decls >>
  simp[shape_state_def] >> metis_tac[shape_base_fresh_outputs]
QED

Theorem alloc_run_internal_param_materialization:
  !captured ce.
    alloc_run (\st. shape_state st /\ cenv_shape_ok st ce /\
        EVERY (\(name,is_stack,op). plain_operand st op) captured)
      (materialize_internal_params ce captured)
      (\ce' st. shape_state st /\ cenv_shape_ok st ce' /\
        ce'.ce_return_pc = ce.ce_return_pc /\ fresh_outputs st)
Proof
  rpt gen_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any structlit_materialize_internal_params_shape >>
  irule_at Any alloc_run_materialize_internal_params >>
  simp[shape_state_def] >> metis_tac[shape_base_fresh_outputs]
QED

Theorem structlit_internal_body_env_shape:
  !st ce imm.
    cenv_shape_ok st ce /\ (!b. imm = SOME b ==> plain_operand st b) ==>
    cenv_shape_ok st (ce with <|ce_imm_alloca := imm; ce_alloca_locals := T|>)
Proof
  rw[cenv_shape_ok_def] >> metis_tac[]
QED

Theory bodyPtrStructLitOwnershipInternalFrame
Ancestors
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipInternalEntry
  bodyPtrStructLitOwnershipInternalShape loweringShapeDefs loweringShapeRules
  loweringShapeProps bodyPtrStructLitOwnershipSteps

Theorem alloc_run_internal_param_capture_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st)
    (compile_internal_param_decls params idx)
    (\r st. shape_state st /\ R st /\
      EVERY (\(name,is_stack,op). plain_operand st op) (FST r) /\
      fresh_outputs st)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_frame >>
  irule_at Any structlit_compile_internal_param_decls_shape >>
  simp[SF ETA_ss] >> irule_at Any alloc_run_internal_param_capture >>
  qexists `R` >> simp[]
QED

Theorem alloc_run_internal_param_materialization_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st /\ cenv_shape_ok st ce /\
      EVERY (\(name,is_stack,op). plain_operand st op) captured)
    (materialize_internal_params ce captured)
    (\ce' st. shape_state st /\ R st /\ cenv_shape_ok st ce' /\
      ce'.ce_return_pc = ce.ce_return_pc /\ fresh_outputs st)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_frame >>
  irule_at Any structlit_materialize_internal_params_shape >>
  simp[SF ETA_ss] >>
  irule_at Any (SRULE [SF ETA_ss] alloc_run_internal_param_materialization) >>
  qexists `R` >> simp[]
QED

Theorem structlit_optional_plain_shape_stable:
  shape_stable (\st. !b. imm = SOME b ==> plain_operand st b)
Proof
  rw[shape_stable_def] >> metis_tac[plain_operand_mono]
QED

(* Consumer probe: immutable framing supplies the actual body record update. *)
Theorem alloc_run_internal_materialization_body_env:
  alloc_run (\st. shape_state st /\
      (!b. imm = SOME b ==> plain_operand st b) /\ cenv_shape_ok st ce /\
      EVERY (\(name,is_stack,op). plain_operand st op) captured)
    (materialize_internal_params ce captured)
    (\ce' st. shape_state st /\
      cenv_shape_ok st (ce' with <|ce_imm_alloca := imm; ce_alloca_locals := T|>) /\
      ce'.ce_return_pc = ce.ce_return_pc /\ fresh_outputs st)
Proof
  irule alloc_run_conseq >>
  irule_at Any alloc_run_internal_param_materialization_frame >>
  irule_at Any structlit_optional_plain_shape_stable >>
  simp[] >> metis_tac[structlit_internal_body_env_shape]
QED

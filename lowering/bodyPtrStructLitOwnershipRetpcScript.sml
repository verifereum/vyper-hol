Theory bodyPtrStructLitOwnershipRetpc
Ancestors
  bodyPtrStructLitOwnershipShape bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFreshness loweringShapeRules loweringShapeDefs

Theorem alloc_run_retpc_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st /\ internal_label_ok st.cs_current_bb)
    (emit_op RETPC_PARAM [Lit w])
    (\pc st. shape_state st /\ R st /\ retpc_operand st pc /\ fresh_outputs st)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any shape_step_emit_op_retpc >>
  irule_at Any alloc_run_emit_op >>
  simp[shape_state_def] >> metis_tac[shape_base_fresh_outputs]
QED

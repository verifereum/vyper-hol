Theory bodyPtrStructLitOwnershipShape
Ancestors bodyPtrStructLitOwnershipSteps loweringShapeDefs loweringShapeRules

Theorem alloc_run_shape_join:
  shape_step internal LP P f Q /\ alloc_run R f Post ==>
  alloc_run (\st. shape_state st /\ P st /\ R st) f
    (\v st. shape_state st /\ Q v st /\ Post v st)
Proof
  rw[alloc_run_def, shape_step_def] >> metis_tac[]
QED

Theorem alloc_run_shape_base_join:
  shape_base_step internal LP P f Q /\ alloc_run R f Post ==>
  alloc_run (\st. shape_base_state st /\ P st /\ R st) f
    (\v st. shape_base_state st /\ Q v st /\ Post v st)
Proof
  rw[alloc_run_def, shape_base_step_def] >> metis_tac[]
QED

Theorem alloc_run_emit_op_shape_probe:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!id outs. lowered_inst_ok internal (mk_inst id opc ops outs)) ==>
  alloc_run
    (\st. shape_state st /\ (R st /\ EVERY (label_or_plain st) ops) /\
           shape_base_state st)
    (emit_op opc ops)
    (\v st. shape_state st /\ (R st /\ plain_operand st v) /\ T)
Proof
  strip_tac >> ho_match_mp_tac alloc_run_shape_join >>
  irule_at Any alloc_run_emit_op >>
  irule shape_step_emit_op >> simp[]
QED

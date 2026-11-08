Theory bodyPtrStructLitOwnershipLock
Ancestors
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipShape
  bodyPtrStructLitOwnershipSteps bodyPtrStructLitOwnershipFreshness
  loweringShapeProps loweringShapeDefs context compileEnv

Theorem alloc_run_nonreentrant_lock:
  alloc_run fresh_outputs (compile_nonreentrant_lock nkey use_trans is_view)
    (\u st. fresh_outputs st)
Proof
  Cases_on `use_trans` >> Cases_on `is_view` >>
  simp[compile_nonreentrant_lock_def, comp_ignore_bind_def] >>
  ntac 4 (irule alloc_run_bind >> qexists `\u st. fresh_outputs st` >>
    reverse conj_tac
    >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
            SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
    gen_tac >> simp[comp_ignore_bind_def]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem alloc_run_nonreentrant_lock_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st)
    (compile_nonreentrant_lock nkey use_trans is_view)
    (\u st. shape_state st /\ R st /\ fresh_outputs st)
Proof
  strip_tac >>
  `alloc_run shape_state (compile_nonreentrant_lock nkey use_trans is_view)
     (\u st. fresh_outputs st)` by
    (irule alloc_run_conseq >> irule_at Any alloc_run_nonreentrant_lock >>
     simp[shape_state_def, shape_base_fresh_outputs]) >>
  irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_frame >>
  irule_at Any compile_nonreentrant_lock_shape >>
  simp[SF ETA_ss] >> goal_assum (drule_at Any) >>
  qexists `R` >> simp[]
QED

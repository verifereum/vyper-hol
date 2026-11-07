Theory bodyPtrStructLitOwnershipStmtLoops
Ancestors bodyPtrStructLitOwnershipStmtHelpers bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipLoops
  bodyPtrStructLitCompilerOwnership compileEnv emitHelper stmtLowering
  loweringShapeDefs loweringShapeRules bodyPtrStructLitOwnershipShape
  bodyPtrStructLitLoopShapeEmit

Theorem alloc_run_emit_jmp_if_not_terminated:
  alloc_run (\s. T) (emit_jmp_if_not_terminated lbl) (\u s. T)
Proof
  rw[alloc_run_def, emit_jmp_if_not_terminated_def,
    comp_bind_def, comp_get_def] >>
  Cases_on `block_is_terminated s` >> gvs[comp_return_def, alloc_frame_refl] >>
  mp_tac (Q.INST [`opc` |-> `JMP`, `ops` |-> `[Label lbl]`, `outs` |-> `[]`]
    alloc_run_emit_inst) >> simp[alloc_run_def] >>
  disch_then drule >> simp[]
QED

Theorem alloc_run_emit_jmp_if_not_terminated_frame:
  shape_stable R /\ compiler_label lbl ==>
  alloc_run (\s. shape_state s /\ R s)
    (emit_jmp_if_not_terminated lbl) (\u s. shape_state s /\ R s)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any alloc_run_emit_jmp_if_not_terminated >> simp[] >>
  qexistsl [`F`, `\u s. R s`, `R`, `compiler_label`] >> simp[] >>
  simp[emit_jmp_if_not_terminated_def] >>
  irule shape_step_bind >> qexists `\cs s. R s` >> reverse conj_tac
  >- simp[shape_step_def, comp_get_def, shape_extends_refl] >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC
  >- (irule shape_step_return >> simp[]) >>
  simp[SF ETA_ss] >> irule (SRULE [SF ETA_ss] loop_shape_jmp) >> simp[]
QED

Theory bodyPtrStructLitOwnershipImmutable
Ancestors
  bodyPtrStructLitOwnershipInternalShape bodyPtrStructLitOwnershipFrame
  bodyPtrStructLitOwnershipShape bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFreshness context emitHelper compileEnv
  loweringShapeDefs loweringShapeRules

Theorem structlit_fixed_region_emit_op[local]:
  compile_fixed_region_with_id sz st = (r,st') ==>
  emit_op ASSIGN [Lit 0w] st = ((SND r).buf_operand,st')
Proof
  simp[compile_fixed_region_with_id_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[]
QED

Theorem alloc_run_fixed_region:
  alloc_run fresh_outputs (compile_fixed_region_with_id sz)
    (\r st. fresh_outputs st)
Proof
  rw[alloc_run_def] >> drule structlit_fixed_region_emit_op >> strip_tac >>
  mp_tac (Q.INST [`opc` |-> `ASSIGN`, `ops` |-> `[Lit 0w]`]
    alloc_run_emit_op_fresh) >>
  simp[alloc_run_def] >> disch_then drule_all >> simp[]
QED

Theorem alloc_run_fixed_region_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st) (compile_fixed_region_with_id sz)
    (\r st. shape_state st /\ R st /\
      plain_operand st (SND r).buf_operand /\ fresh_outputs st)
Proof
  strip_tac >>
  `alloc_run shape_state (compile_fixed_region_with_id sz)
     (\r st. fresh_outputs st)` by
    (irule alloc_run_conseq >> irule_at Any alloc_run_fixed_region >>
     simp[shape_state_def, shape_base_fresh_outputs]) >>
  irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_frame >>
  irule_at Any structlit_compile_fixed_region_with_id_shape >>
  simp[SF ETA_ss] >> goal_assum (drule_at Any) >>
  qexists `R` >> simp[shape_state_def] >> metis_tac[shape_base_fresh_outputs]
QED

Theorem alloc_run_internal_immutable_frame:
  shape_stable R ==>
  alloc_run (\st. shape_state st /\ R st)
    (if is_ctor /\ imm_len > 0 then
       do r <- compile_fixed_region_with_id imm_len;
          return (SOME (SND r).buf_operand) od
     else return NONE)
    (\imm st. shape_state st /\ R st /\
      (!b. imm = SOME b ==> plain_operand st b) /\ fresh_outputs st)
Proof
  strip_tac >> IF_CASES_TAC >> simp[]
  >- (irule alloc_run_bind >>
      qexists `\r st. shape_state st /\ R st /\
        plain_operand st (SND r).buf_operand /\ fresh_outputs st` >>
      reverse conj_tac >- simp[alloc_run_fixed_region_frame] >>
      gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl,
       shape_state_def, shape_base_fresh_outputs]
QED

Theory bodyPtrStructLitOwnershipIfexpFrame
Ancestors bodyPtrStructLitOwnershipIfexpArm bodyPtrStructLitOwnershipStructFrame
  bodyPtrStructLitOwnershipPrimitives bodyPtrStructLitOwnershipSteps
  loweringShapeProps loweringShapeDefs loweringShapeRules exprLowering context compileEnv

Theorem alloc_run_alloc_buffer_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s) (compile_alloc_buffer n)
    (\b s. shape_state s /\ R s /\ plain_operand s b.buf_operand)
Proof
  strip_tac >> irule alloc_run_conseq >>
  irule_at Any (Q.INST [`internal` |-> `F`] alloc_run_fresh_shape_frame) >>
  irule_at Any compile_alloc_buffer_shape >>
  simp[alloc_run_compile_alloc_buffer] >> qexists `R` >> simp[]
QED

Theorem alloc_run_compile_ifexp_arm_frame:
  shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ value_shape_ok s vv)
    (compile_ifexp_arm ce rt at vv)
    (\op s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s op)
Proof
  strip_tac >> simp[compile_ifexp_arm_def] >> IF_CASES_TAC
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. R s /\ cenv_shape_ok s ce`]
        alloc_run_unwrap_value_frame) >> qexists `R` >>
      simp[shape_stable_conj, cenv_shape_ok_stable]) >>
  simp[comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\b s. shape_state s /\
    (R s /\ cenv_shape_ok s ce /\ value_shape_ok s vv) /\ plain_operand s b.buf_operand` >>
  reverse conj_tac
  >- (ho_match_mp_tac alloc_run_alloc_buffer_frame >>
      simp[shape_stable_conj, cenv_shape_ok_stable, value_shape_ok_stable]) >>
  qx_gen_tac `buf` >> simp[] >>
  irule alloc_run_bind >>
  qexists `\src s. shape_state s /\
    (R s /\ cenv_shape_ok s ce /\ plain_operand s buf.buf_operand) /\ plain_operand s src` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. R s /\ plain_operand s buf.buf_operand`]
        alloc_run_unwrap_value_frame) >>
      qexistsl [`buf`, `\s. R s /\ cenv_shape_ok s ce`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands)]) >>
  qx_gen_tac `src` >> simp[] >>
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\
    (R s /\ cenv_shape_ok s ce /\ plain_operand s buf.buf_operand) /\ T` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >>
      irule_at Any (Q.INST [`R` |-> `\s. R s /\ cenv_shape_ok s ce /\ plain_operand s buf.buf_operand`]
        alloc_run_store_memory_frame) >> qexistsl [`buf`, `R`] >>
      simp[shape_stable_conj, cenv_shape_ok_stable,
        SRULE [] (Q.SPEC `[buf.buf_operand]` shape_stable_plain_operands)]) >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

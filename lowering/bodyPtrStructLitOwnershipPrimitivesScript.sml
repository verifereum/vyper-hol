Theory bodyPtrStructLitOwnershipPrimitives
Ancestors bodyPtrStructLitOwnershipShape bodyPtrStructLitOwnershipSlots
  loweringShapeProps context bodyPtrStructLitOwnershipSteps compileEnv loweringStateRelDefs
  emitHelper loweringShapeDefs bodyPtrStructLitCompilerOwnership list
  bodyPtrStructLitOwnershipFreshness

Theorem alloc_run_compile_alloc_buffer:
  alloc_run fresh_outputs (compile_alloc_buffer n) (\v st. fresh_outputs st)
Proof
  rw[alloc_run_def, compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  Cases_on `emit_op ALLOCA [Lit (n2w n)] st` >> gvs[] >>
  mp_tac (Q.INST [`opc` |-> `ALLOCA`, `ops` |-> `[Lit (n2w n)]`]
    alloc_run_emit_op_fresh) >>
  simp[alloc_run_def] >> disch_then drule_all >> simp[]
QED

Theorem alloc_run_compile_alloc_buffer_shape:
  alloc_run (\st. shape_state st /\ T /\ shape_base_state st)
    (compile_alloc_buffer n)
    (\buf st. shape_state st /\ plain_operand st buf.buf_operand /\ T)
Proof
  irule alloc_run_conseq >>
  irule_at Any (Q.INST [`LP` |-> `compiler_label`] alloc_run_shape_join) >>
  irule_at Any alloc_run_compile_alloc_buffer >>
  irule_at Any compile_alloc_buffer_shape >>
  simp[shape_base_fresh_outputs]
QED

Theorem alloc_run_fresh_vars:
  !n. alloc_run shape_base_state (fresh_vars n)
    (\xs st. shape_base_state st /\
      EVERY (\x. not_fresh_at st x /\ ~alloc_owned st x) xs)
Proof
  Induct
  >- simp[alloc_run_def, fresh_vars_def, comp_return_def, alloc_frame_refl] >>
  rw[alloc_run_def, fresh_vars_def, comp_bind_def, comp_return_def] >>
  Cases_on `fresh_var st` >> Cases_on `fresh_vars n r` >> gvs[] >>
  `shape_base_state r` by
    (gvs[fresh_var_def, shape_base_state_def, state_insts_def,
         all_blocks_def, not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  `alloc_writers_unique r /\ alloc_frame st r` by
    (mp_tac alloc_run_fresh_var >> simp[alloc_run_def] >>
     disch_then drule_all >> simp[]) >>
  qpat_x_assum `alloc_run _ _ _` (mp_tac o REWRITE_RULE [alloc_run_def]) >>
  disch_then drule_all >> strip_tac >> gvs[] >>
  drule_all fresh_var_nonowned >> strip_tac >>
  metis_tac[alloc_frame_trans, alloc_frame_reserved]
QED

Theorem alloc_run_emit_multi_op:
  opc <> ALLOCA ==>
  alloc_run shape_base_state (emit_multi_op opc ops n) (\v st. T)
Proof
  strip_tac >>
  rw[alloc_run_def, emit_multi_op_def, comp_bind_def, comp_return_def] >>
  Cases_on `fresh_vars n st` >> Cases_on `emit_inst opc ops q r` >> gvs[] >>
  mp_tac (Q.SPEC `n` alloc_run_fresh_vars) >>
  simp[alloc_run_def] >> disch_then drule_all >> strip_tac >>
  `EVERY (\x. ~alloc_owned r x) q` by fs[EVERY_MEM] >>
  drule alloc_run_emit_inst >>
  simp[alloc_run_def] >> disch_then drule_all >> strip_tac >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  metis_tac[alloc_frame_trans]
QED

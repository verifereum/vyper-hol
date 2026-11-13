Theory runtimeSymSrcIterCopy
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission runtimeSymSrcContext
  runtimeSymSrcContextCopy runtimeSymSrcContextTyped stmtLowering
  compileEnv context emitHelper loweringShapeDefs venomInst stackPlanTypes list

Theorem runtime_sym_iter_elem_copy:
  runtime_sym_env ce /\ ~is_label_operand src /\ ~is_label_operand dst /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_iter_elem_copy ce src dst sz loc slots dty sty s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  `!b. ce.ce_imm_alloca = SOME b ==> ~is_label_operand b` by
    metis_tac[runtime_sym_env_def] >>
  Cases_on `slots`
  >- (gvs[compile_iter_elem_copy_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >>
      pairarg_tac >> gvs[] >> drule_all runtime_sym_slot_to_memory >> simp[]) >>
  Cases_on `loc = LocMemory`
  >- (gvs[compile_iter_elem_copy_def] >>
      Cases_on `is_word_type dty`
      >- (gvs[comp_bind_def, comp_ignore_bind_def] >> pairarg_tac >> gvs[] >>
          drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
          simp[] >> strip_tac >> drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
      gvs[] >> drule_all runtime_sym_store_memory >> simp[]) >>
  Cases_on `sz <= 32`
  >- (gvs[compile_iter_elem_copy_def, comp_bind_def, comp_ignore_bind_def] >>
      pairarg_tac >> gvs[] >> drule_all runtime_sym_ptr_load >> strip_tac >>
      drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
  Cases_on `loc` >> gvs[compile_iter_elem_copy_def]
  >- (drule_all runtime_sym_copy_memory >> simp[])
  >- (drule_all runtime_sym_copy_memory >> simp[])
  >- (drule_all runtime_sym_imm_copy_to_memory >> simp[]) >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
  simp[is_label_operand_def]
QED

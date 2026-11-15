Theory runtimeSymSrcStoreSlotsStatic
Ancestors
  runtimeSymSrcContextCopy runtimeSymSrcEmission runtimeSymSrcContext
  runtimeSymSrcEmissionProbe context compileEnv emitHelper list venomInst

Theorem runtime_sym_store_slots_static:
  ~is_abi_dynamic cenv.ce_struct_fields ty /\
  ~is_label_operand src /\ ~is_label_operand slot /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_slots cenv src slot ty tr s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def] >>
  Cases_on `type_memory_bytes cenv ty DIV 32 = 1`
  >- (simp[comp_bind_def] >> pairarg_tac >> gvs[] >> strip_tac >>
      qpat_x_assum `emit_op _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
      Cases_on `tr` >> gvs[] >>
      qpat_x_assum `emit_void _ _ _ = _`
        (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]) >>
  Cases_on `tr` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[]
  >- (drule_all runtime_sym_memory_to_transient >> simp[])
  >> drule_all runtime_sym_memory_to_storage >> simp[]
QED

Theorem runtime_sym_store_slots_bytestring:
  is_abi_dynamic cenv.ce_struct_fields ty /\ is_bytestring_type ty /\
  ~is_label_operand src /\ ~is_label_operand slot /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_store_slots cenv src slot ty tr s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  strip_tac >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_store_slots_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_bytestring_word_count _ _ = _`
    (mp_then Any mp_tac runtime_sym_bytestring_word_count) >>
  simp[] >> strip_tac >>
  drule_all runtime_sym_word_copy_loop_op >> simp[]
QED

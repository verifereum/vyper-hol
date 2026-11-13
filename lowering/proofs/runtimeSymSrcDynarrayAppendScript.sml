Theory runtimeSymSrcDynarrayAppend
Ancestors
  runtimeSymSrcEmission runtimeSymSrcContextTyped runtimeSymSrcContextCopy
  exprLowering compileEnv emitHelper loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_dynarray_append:
  !ce base_op v ws es et st cap prim load store s u s'.
    ~is_label_operand base_op /\ ~is_label_operand v /\
    load <> CODESIZE /\ load <> CODECOPY /\
    store <> CODESIZE /\ store <> CODECOPY /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_dynarray_append ce base_op v ws es et st cap prim load store s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')
Proof
  rpt gen_tac >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> rpt strip_tac >>
  qpat_assum `emit_op load _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `emit_op LT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_void ASSERT _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[] >> strip_tac >>
  qpat_assum `emit_op ADD [base_op; _] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op MUL _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op ADD [data_ptr; _] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[] >> strip_tac >>
  qpat_assum `(if prim then _ else _) _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `loc = LocMemory` >>
  disch_then assume_tac >>
  rename1 `(if prim then _ else _) store_s = (store_u,store_s')` >>
  `EVERY runtime_sym_inst (state_insts store_s')` by
    (Cases_on `prim` >> gvs[]
     >- (qpat_assum `emit_void store [elem_ptr; v] _ = _`
           (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]) >>
     Cases_on `loc = LocMemory` >>
     gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> gvs[]
     >- (drule_all runtime_sym_store_memory >> simp[]) >>
     drule_all runtime_sym_word_copy_loop >> simp[]) >>
  qpat_assum `emit_op ADD [len_op; _] store_s' = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_void store [base_op; new_len] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >> simp[]
QED

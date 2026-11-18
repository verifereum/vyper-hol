Theory runtimeSymSrcLiteralEnv
Ancestors
  runtimeSymSrcContext runtimeSymSrcInterfaces runtimeSymSrcEmission
  exprLowering compileEnv context emitHelper loweringShapeDefs list venomInst stackPlanTypes

Theorem runtime_sym_store_byte_chunks:
  !ptr bs off s u s'.
  ~is_label_operand ptr /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_store_byte_chunks ptr bs off s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  recInduct compile_store_byte_chunks_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once compile_store_byte_chunks_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
  simp[is_label_operand_def] >> strip_tac >>
  first_x_assum irule >> simp[] >> goal_assum drule >> simp[]
QED

Theorem runtime_sym_bytelike_literal:
  EVERY runtime_sym_inst (state_insts s) /\
  compile_bytelike_literal bs n s = (b,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand b.buf_operand
Proof
  simp[compile_bytelike_literal_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_store_byte_chunks >> simp[]
QED

Theorem runtime_sym_literal_vv:
  !ty lit s v s'. EVERY runtime_sym_inst (state_insts s) /\
  compile_literal_vv ty lit s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ runtime_sym_value v
Proof
  Cases_on `lit` >> simp[compile_literal_vv_def, comp_return_def,
    runtime_sym_value_def, is_label_operand_def]
  >- (Cases_on `b` >> simp[compile_literal_vv_def, comp_return_def,
        runtime_sym_value_def, is_label_operand_def]) >>
  Cases_on `ty` >> simp[compile_literal_vv_def, comp_return_def,
    runtime_sym_value_def, is_label_operand_def, comp_bind_def] >>
  TRY (Cases_on `b` >>
    simp[compile_literal_vv_def, comp_return_def, runtime_sym_value_def,
         is_label_operand_def, comp_bind_def] >>
    TRY (Cases_on `b'` >> simp[compile_literal_vv_def, comp_return_def,
      runtime_sym_value_def, is_label_operand_def, comp_bind_def])) >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `compile_bytelike_literal bytes len st` >>
  Cases_on `compile_bytelike_literal bytes len st` >> gvs[] >>
  drule_all runtime_sym_bytelike_literal >>
  simp[runtime_sym_value_def, base_ptr_def]
QED

Theorem runtime_sym_env_var:
  !item s op s'. EVERY runtime_sym_inst (state_insts s) /\
  compile_env_var item s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `item` >> simp[compile_env_var_def, comp_bind_def] >>
  rpt gen_tac >> strip_tac
  >>~- ([`emit_op _ _ _ = _`],
    drule_at (Pat `emit_op _ _ _ = _`) runtime_sym_emit_op >> simp[]) >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  qpat_assum `emit_op NUMBER _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[] >> strip_tac >>
  qpat_assum `emit_op SUB _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op BLOCKHASH _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >> simp[]
QED

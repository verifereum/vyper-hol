Theory runtimeSymSrcBuiltinHash
Ancestors
  runtimeSymSrcBuiltinData runtimeSymSrcContext runtimeSymSrcEmission
  runtimeSymSrcInterfaces
  builtinHashing context compileEnv emitHelper loweringShapeDefs venomInst
  list stackPlanTypes

Theorem runtime_sym_keccak256_bytesm:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_keccak256_bytesm v m s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_keccak256_bytesm_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  gvs[emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_keccak256_word:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_keccak256_word v s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_keccak256_word_def, GSYM compile_keccak256_bytesm_def] >>
  metis_tac[runtime_sym_keccak256_bytesm]
QED

Theorem runtime_sym_method_id_hash:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_method_id_hash ty v s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `ty` >> simp[compile_method_id_hash_def]
  >~ [`BaseT bt`] >- (
    Cases_on `bt` >> simp[compile_method_id_hash_def]
    >~ [`BytesT sz`] >- (
      Cases_on `sz` >> simp[compile_method_id_hash_def] >>
      metis_tac[runtime_sym_keccak256_bytesm, runtime_sym_keccak256_bytes]) >>
    metis_tac[runtime_sym_keccak256_bytes]) >>
  metis_tac[runtime_sym_keccak256_bytes]
QED

Theorem runtime_sym_method_id_runtime:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_method_id_runtime ty v b s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  Cases_on `b` >>
  simp[compile_method_id_runtime_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all runtime_sym_method_id_hash >> strip_tac >>
  qpat_x_assum `compile_method_id_hash _ _ _ = _` kall_tac >>
  qpat_assum `emit_op SHR _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `emit_op SHL _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >> gvs[] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  gvs[emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_sha256_bytesm:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_sha256_bytesm v m s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_sha256_bytesm_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ s = _` kall_tac >>
  qpat_assum `emit_void MSTORE _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_void) >>
  simp[] >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  gvs[emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_sha256_word:
  ~is_label_operand v /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_sha256_word v s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_sha256_word_def, GSYM compile_sha256_bytesm_def] >>
  metis_tac[runtime_sym_sha256_bytesm]
QED

Theorem runtime_sym_sha256_bytes:
  ~is_label_operand p /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_sha256_bytes p s = (op,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op
Proof
  simp[compile_sha256_bytes_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  qpat_assum `emit_op MLOAD [p] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[] >> strip_tac >>
  qpat_assum `emit_op ADD _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  simp[is_label_operand_def] >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  gvs[emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND,
      EVERY_APPEND, runtime_sym_inst_def, mk_inst_def, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

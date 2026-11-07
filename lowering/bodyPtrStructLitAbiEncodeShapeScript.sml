Theory bodyPtrStructLitAbiEncodeShape
Ancestors bodyPtrStructLitAbiEncodeShapeBase bodyPtrStructLitTargetScalar
  loweringShapeProps loweringShapeRules loweringShapeDefs abiEncoder
  context compileEnv venomInst stackPlanTypes unitShapeDefs list

Theorem abi_encode_and_shape:
  shape_stable R ==>
  shape_step F compiler_label
    (\s. R s /\ EVERY (plain_operand s) ops) (emit_op AND ops)
    (\v s. R s /\ plain_operand s v)
Proof
  strip_tac >> irule shape_step_conseq >>
  irule_at Any shape_step_frame >> irule_at Any shape_step_emit_op_pre >>
  qexistsl [`R`, `\s. EVERY (plain_operand s) ops`, `compiler_label`] >>
  gvs[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
    raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
    is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
    is_terminator_def, EVERY_MEM, plain_operand_def] >>
  rpt strip_tac >> rpt (CASE_TAC >> gvs[EVERY_MEM, is_label_operand_def]) >>
  metis_tac[is_label_operand_def]
QED

Theorem abi_encode_and_bind:
  shape_stable R /\ (!s. R s ==> EVERY (plain_operand s) ops) /\
  (!v. shape_step F compiler_label (\s. R s /\ plain_operand s v) (k v) Q) ==>
  shape_step F compiler_label R (comp_bind (emit_op AND ops) k) Q
Proof
  strip_tac >> irule shape_step_bind >>
  qexists `\v s. R s /\ plain_operand s v` >> simp[] >>
  irule shape_step_conseq >> irule_at Any abi_encode_and_shape >>
  qexists `R` >> simp[]
QED

Theorem abi_encode_bytes_shape:
  shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (compile_abi_encode_to_buf dst src (AbiBytestring max_len))
    (\v s. plain_operand s v)
Proof
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  irule target_scalar_op_bind >> simp[shape_stable_conj] >> qx_gen_tac `len_op` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `ceil_op` >>
  irule abi_encode_and_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `rounded` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `last_ptr` >> suspend "store"
QED

Resume abi_encode_bytes_shape[store]:
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def, is_label_operand_def] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `copy_len` >>
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def, is_label_operand_def] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `ceil2` >>
  irule abi_encode_and_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `rounded2` >>
  irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
  qexists `\s. T` >> simp[shape_stable_def]
QED

Finalise abi_encode_bytes_shape

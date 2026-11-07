Theory bodyPtrStructLitAbiEncodeShapeBase
Ancestors bodyPtrStructLitTargetScalar bodyPtrStructLitAbiPrefixProbe
  loweringShapeProps loweringShapeRules loweringShapeDefs abiEncoder
  context compileEnv venomInst stackPlanTypes unitShapeDefs emitHelper

Theorem abi_encode_static_shape:
  shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (compile_abi_encode_static dst src) (\len s. plain_operand s len)
Proof
  simp[compile_abi_encode_static_def] >> irule target_scalar_op_bind >>
  simp[shape_stable_conj,
    SRULE [] (Q.SPEC `[dst]` shape_stable_plain_operands),
    SRULE [] (Q.SPEC `[src]` shape_stable_plain_operands)] >>
  gen_tac >> irule shape_step_ignore_bind >> qexists `\u s. T` >> reverse conj_tac
  >- (irule shape_step_emit_void_pre >>
      simp[lowered_inst_ok_def, mk_inst_def, label_or_plain_def,
        raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
        is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
        is_terminator_def, plain_operand_def, is_label_operand_def]) >>
  gen_tac >> irule shape_step_return >>
  simp[plain_operand_def, is_label_operand_def]
QED

Theorem abi_encode_static_info_shape:
  shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (compile_abi_encode_static_info dst src info) (\len s. plain_operand s len)
Proof
  Cases_on `info` >> simp[compile_abi_encode_static_info_def, abi_encode_static_shape] >>
  TRY (irule shape_step_return >> simp[plain_operand_def, is_label_operand_def] >> NO_TAC) >>
  mp_tac abi_prefix_copy_shape >> simp[Once compile_abi_encode_child_def]
QED

Theorem abi_encode_emit_inst_bind[local]:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!id. lowered_inst_ok F (mk_inst id opc ops [])) /\
  (!s. R s ==> EVERY (label_or_plain s) ops) /\
  (!u. shape_step F compiler_label R (k u) Q) ==>
  shape_step F compiler_label R (comp_bind (emit_inst opc ops []) k) Q
Proof
  strip_tac >> irule shape_step_bind >> qexists `\u s. R s` >> simp[SF ETA_ss] >>
  irule shape_step_conseq >> irule_at Any shape_step_emit_inst >>
  qexistsl [`R`, `compiler_label`] >> simp[]
QED

Theorem abi_encode_new_block_bind[local]:
  shape_stable R /\ compiler_label lbl /\
  (!u. shape_step F compiler_label R (k u) Q) ==>
  shape_step F compiler_label R (comp_bind (new_block lbl) k) Q
Proof
  strip_tac >> irule shape_step_bind >> qexists `\u s. R s` >> simp[SF ETA_ss] >>
  irule (SRULE [SF ETA_ss] shape_step_new_block) >> simp[]
QED

Theorem abi_encode_plain_stable[local,simp]:
  shape_stable (\s. plain_operand s op)
Proof
  mp_tac (Q.SPEC `[op]` shape_stable_plain_operands) >> simp[]
QED

Theorem abi_encode_void_bind[local]:
  shape_stable R /\ ~MEM opc [GAS; RETPC_PARAM; RET; CALL; STATICCALL] /\
  (!s id. R s ==> lowered_inst_ok F (mk_inst id opc ops [])) /\
  (!s. R s ==> EVERY (label_or_plain s) ops) /\
  (!u. shape_step F compiler_label R (k u) Q) ==>
  shape_step F compiler_label R (comp_bind (emit_void opc ops) k) Q
Proof
  strip_tac >> irule shape_step_bind >> qexists `\u s. R s` >> simp[SF ETA_ss] >>
  irule shape_step_conseq >> irule_at Any shape_step_frame >>
  irule_at Any shape_step_emit_void_pre >>
  qexistsl [`R`, `R`, `compiler_label`] >> simp[] >> metis_tac[]
QED

Theorem abi_encode_literal_plain[local,simp]:
  plain_operand s (Lit w)
Proof
  simp[plain_operand_def, is_label_operand_def]
QED

Theorem abi_encode_jmp_bind[local]:
  shape_stable R /\ compiler_label lbl /\
  (!u. shape_step F compiler_label R (k u) Q) ==>
  shape_step F compiler_label R (comp_bind (emit_inst JMP [Label lbl] []) k) Q
Proof
  strip_tac >> irule abi_encode_emit_inst_bind >>
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
    inst_shape_ok_def, inst_jump_labels_ok_def, is_param_opcode_def,
    is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
    label_or_plain_def, jump_label_ok_def, is_label_operand_def]
QED

Theorem abi_encode_jnz_bind[local]:
  shape_stable R /\ compiler_label yes /\ compiler_label no /\ yes <> no /\
  (!s. R s ==> plain_operand s test) /\
  (!u. shape_step F compiler_label R (k u) Q) ==>
  shape_step F compiler_label R
    (comp_bind (emit_inst JNZ [test; Label yes; Label no] []) k) Q
Proof
  strip_tac >> Cases_on `is_label_operand test`
  >- (gvs[plain_operand_def, shape_step_def] >> metis_tac[]) >>
  irule abi_encode_emit_inst_bind >>
  simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def,
    inst_shape_ok_def, inst_jump_labels_ok_def, is_param_opcode_def,
    is_read0_opcode_def, label_positions_ok_def, is_terminator_def,
    label_or_plain_def, jump_label_ok_def] >>
  gvs[plain_operand_def, is_label_operand_def] >> metis_tac[is_label_operand_def]
QED

Theorem abi_encode_dyn_static_loop_shape:
  shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s src /\ plain_operand s len)
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
    (\v s. plain_operand s v)
Proof
  simp[compile_abi_encode_dyn_static_loop_def] >> irule shape_step_bind >>
  qexists `\b s. plain_operand s dst /\ plain_operand s src /\
    plain_operand s len /\ plain_operand s b.buf_operand` >> conj_tac
  >- suspend "labels" >>
  irule shape_step_conseq >> irule_at Any shape_step_frame >>
  irule_at Any compile_alloc_buffer_shape >>
  qexists `\s. plain_operand s dst /\ plain_operand s src /\ plain_operand s len` >>
  simp[GSYM CONJ_ASSOC, shape_stable_conj]
QED

Resume abi_encode_dyn_static_loop_shape[labels]:
  qx_gen_tac `b` >> simp[comp_ignore_bind_def] >>
  irule abi_encode_void_bind >>
  simp[GSYM CONJ_ASSOC, shape_stable_conj] >> conj_tac
  >- (simp[lowered_inst_ok_def, mk_inst_def,
      raw_opcode_ok_def, inst_shape_ok_def, inst_jump_labels_ok_def,
      is_param_opcode_def, is_read0_opcode_def, label_positions_ok_def,
      is_terminator_def, plain_operand_def, is_label_operand_def]) >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def, is_label_operand_def] >>
  irule shape_step_bind >>
  qexists `\l s. (plain_operand s dst /\ plain_operand s src /\
    plain_operand s len /\ plain_operand s b.buf_operand) /\ compiler_label l` >>
  reverse conj_tac >- (ho_match_mp_tac shape_step_fresh_label >> simp[GSYM CONJ_ASSOC, shape_stable_conj]) >>
  qx_gen_tac `hdr` >> reverse (Cases_on `compiler_label hdr`)
  >- simp[shape_step_def] >> simp[] >> suspend "body_label"
QED

Resume abi_encode_dyn_static_loop_shape[body_label]:
  irule shape_step_bind >>
  qexists `\l s. (plain_operand s dst /\ plain_operand s src /\
    plain_operand s len /\ plain_operand s b.buf_operand) /\
    compiler_label l /\ label_sfx "enc_dyn_body" l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label_sfx >> simp[GSYM CONJ_ASSOC, shape_stable_conj]) >>
  qx_gen_tac `body_lbl` >>
  reverse (Cases_on `compiler_label body_lbl /\ label_sfx "enc_dyn_body" body_lbl`)
  >- simp[shape_step_def] >> simp[] >>
  irule shape_step_bind >>
  qexists `\l s. (plain_operand s dst /\ plain_operand s src /\
    plain_operand s len /\ plain_operand s b.buf_operand) /\
    compiler_label l /\ label_sfx "enc_dyn_exit" l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label_sfx >> simp[GSYM CONJ_ASSOC, shape_stable_conj]) >>
  qx_gen_tac `exit` >>
  reverse (Cases_on `compiler_label exit /\ label_sfx "enc_dyn_exit" exit`)
  >- simp[shape_step_def] >> simp[] >>
  `exit <> body_lbl` by (irule label_sfx_distinct >>
    qexistsl [`"enc_dyn_exit"`, `"enc_dyn_body"`] >> simp[]) >>
  suspend "header"
QED

Resume abi_encode_dyn_static_loop_shape[header]:
  irule abi_encode_jmp_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  irule abi_encode_new_block_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `index` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `cmp` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac
  >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `test` >>
  irule abi_encode_jnz_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule abi_encode_new_block_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (simp[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  suspend "loop_body"
QED

Resume abi_encode_dyn_static_loop_shape[loop_body]:
  irule target_scalar_op_bind >> simp[shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `idx` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `src_data` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >> suspend "offset"
QED

Resume abi_encode_dyn_static_loop_shape[offset]:
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `src_off` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `child_src` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `dst_data` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `dst_off` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `child_dst` >> suspend "encode_child"
QED

Resume abi_encode_dyn_static_loop_shape[encode_child]:
  irule shape_step_bind >>
  qexists `\u s. plain_operand s src /\ plain_operand s b.buf_operand /\ plain_operand s idx` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      irule_at Any abi_encode_static_info_shape >>
      qexists `\s. plain_operand s src /\ plain_operand s b.buf_operand /\ plain_operand s idx` >> simp[shape_stable_conj]) >>
  gen_tac >> BETA_TAC >> irule target_scalar_op_bind >> simp[shape_stable_conj] >>
  qx_gen_tac `new_i` >> irule abi_encode_void_bind >> simp[shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def, is_label_operand_def] >>
  irule abi_encode_jmp_bind >> simp[shape_stable_conj] >>
  irule abi_encode_new_block_bind >> simp[shape_stable_conj] >>
  irule target_scalar_op_bind >> simp[shape_stable_conj] >>
  qx_gen_tac `len_exit` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `payload` >> suspend "last_add"
QED

Resume abi_encode_dyn_static_loop_shape[last_add]:
  irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
  qexists `\s. T` >> simp[shape_stable_def]
QED

Finalise abi_encode_dyn_static_loop_shape

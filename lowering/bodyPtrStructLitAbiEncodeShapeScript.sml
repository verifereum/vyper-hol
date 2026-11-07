Theory bodyPtrStructLitAbiEncodeShape
Ancestors bodyPtrStructLitAbiEncodeShapeBase bodyPtrStructLitTargetScalar
  bodyPtrStructLitAbiPrefixProbe
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

Theorem abi_encode_shape_mutual:
  (!dst cp ci dyn off dp. shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s cp /\ plain_operand s dp)
    (compile_abi_encode_child dst cp ci dyn off dp) (\v s. plain_operand s v)) /\
  (!dst src info. shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (compile_abi_encode_to_buf dst src info) (\v s. plain_operand s v)) /\
  (!dst src es so ho dp. shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s src /\ plain_operand s dp)
    (compile_abi_encode_complex_elems dst src es so ho dp) (\v s. plain_operand s v)) /\
  (!dst src ei asz msz len. shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s src /\ plain_operand s len)
    (compile_abi_encode_dyn_loop dst src ei asz msz len) (\v s. plain_operand s v))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac
  >- suspend "child"
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "copy"
  >- suspend "array"
  >- suspend "empty_complex"
  >- suspend "complex"
  >- suspend "empty_elems"
  >- suspend "elems"
  >> suspend "loop"
QED

Resume abi_encode_shape_mutual[word]:
  simp[Once compile_abi_encode_child_def, abi_encode_static_shape]
QED
Resume abi_encode_shape_mutual[bytes]:
  simp[abi_encode_bytes_shape]
QED
Resume abi_encode_shape_mutual[copy]:
  simp[abi_prefix_copy_shape]
QED
Resume abi_encode_shape_mutual[empty_complex]:
  simp[abi_prefix_empty_shape]
QED
Resume abi_encode_shape_mutual[empty_elems]:
  simp[Once compile_abi_encode_child_def] >> rpt gen_tac >>
  irule shape_step_return >> simp[]
QED
Resume abi_encode_shape_mutual[child]:
  rpt gen_tac >> reverse (Cases_on `dyn`) >> simp[] >> strip_tac
  >- (simp[Once compile_abi_encode_child_def] >>
      irule target_scalar_op_bind >> simp[shape_stable_conj] >> gen_tac >>
      irule shape_step_conseq >> first_x_assum (irule_at Any) >> simp[]) >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  irule target_scalar_op_bind >> simp[shape_stable_conj] >> qx_gen_tac `slot_ptr` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `dyn_ofst` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `child_dst` >>
  irule shape_step_bind >>
  qexists `\v s. (plain_operand s dp /\ plain_operand s slot_ptr /\
    plain_operand s dyn_ofst) /\ plain_operand s v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      first_x_assum (irule_at Any) >>
      qexists `\s. plain_operand s dp /\ plain_operand s slot_ptr /\ plain_operand s dyn_ofst` >>
      simp[shape_stable_conj]) >>
  qx_gen_tac `child_len` >> simp[] >>
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `new_dyn` >>
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
  irule shape_step_return >> simp[]
QED

Resume abi_encode_shape_mutual[elems]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  irule target_scalar_op_bind >> simp[shape_stable_conj] >> qx_gen_tac `elem_src` >>
  irule shape_step_bind >>
  qexists `\v s. plain_operand s dst /\ plain_operand s src /\ plain_operand s dp` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      first_x_assum (irule_at Any) >>
      qexists `\s. plain_operand s dst /\ plain_operand s src /\ plain_operand s dp` >>
      simp[shape_stable_conj]) >>
  gen_tac >> gvs[arithmeticTheory.ADD_COMM]
QED

Resume abi_encode_shape_mutual[complex]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  IF_CASES_TAC >> gnvs[]
  >- (irule shape_step_bind >>
      qexists `\b s. (plain_operand s dst /\ plain_operand s src) /\
        plain_operand s b.buf_operand` >> reverse conj_tac
      >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
          irule_at Any compile_alloc_buffer_shape >>
          qexists `\s. plain_operand s dst /\ plain_operand s src` >> simp[shape_stable_conj]) >>
      qx_gen_tac `buf` >> simp[] >>
      irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
      conj_tac
      >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
          inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
          label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
      conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
      irule shape_step_bind >> qexists `\v s. plain_operand s buf.buf_operand` >>
      reverse conj_tac
      >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
          first_x_assum (irule_at Any) >>
          qexists `\s. plain_operand s buf.buf_operand` >> simp[]) >>
      gen_tac >> BETA_TAC >> irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
      qexists `\s. T` >> simp[shape_stable_def]) >>
  irule shape_step_bind >> qexists `\v s. T` >> reverse conj_tac
  >- (irule shape_step_conseq >> first_x_assum (irule_at Any) >> simp[]) >>
  gen_tac >> BETA_TAC >> irule shape_step_return >> simp[]
QED

Resume abi_encode_shape_mutual[array]:
  rpt gen_tac >> strip_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  irule shape_step_bind >>
  qexists `\b s. (plain_operand s dst /\ plain_operand s src) /\ plain_operand s b.buf_operand` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      irule_at Any compile_alloc_buffer_shape >>
      qexists `\s. plain_operand s dst /\ plain_operand s src` >> simp[shape_stable_conj]) >>
  qx_gen_tac `buf` >> simp[] >>
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `len_op` >>
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
  irule shape_step_bind >>
  qexists `\v s. plain_operand s buf.buf_operand /\ plain_operand s v` >> reverse conj_tac
  >- (Cases_on `elem_is_dyn` >> gvs[]
      >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
          first_x_assum (irule_at Any) >>
          qexists `\s. plain_operand s buf.buf_operand` >> simp[]) >>
      irule shape_step_conseq >> irule_at Any shape_step_frame >>
      irule_at Any abi_encode_dyn_static_loop_shape >>
      qexists `\s. plain_operand s buf.buf_operand` >> simp[]) >>
  suspend "array_suffix"
QED

Resume abi_encode_shape_mutual[array_suffix]:
  qx_gen_tac `encoded_size` >> BETA_TAC >>
  irule target_scalar_op_bind >> simp[shape_stable_conj] >> qx_gen_tac `parent_dyn` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `new_parent_dyn` >>
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
  irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
  qexists `\s. T` >> simp[shape_stable_def]
QED

Resume abi_encode_shape_mutual[loop]:
  rpt gen_tac >> strip_tac >>
  gvs[] >> simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >>
  irule shape_step_bind >>
  qexists `\b s. (plain_operand s dst /\ plain_operand s src /\ plain_operand s len) /\
    plain_operand s b.buf_operand` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      irule_at Any compile_alloc_buffer_shape >>
      qexists `\s. plain_operand s dst /\ plain_operand s src /\ plain_operand s len` >>
      simp[shape_stable_conj]) >>
  qx_gen_tac `ibuf` >> simp[] >>
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
  irule shape_step_bind >>
  qexists `\b s. (plain_operand s dst /\ plain_operand s src /\ plain_operand s len /\
    plain_operand s ibuf.buf_operand) /\ plain_operand s b.buf_operand` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      irule_at Any compile_alloc_buffer_shape >>
      qexists `\s. plain_operand s dst /\ plain_operand s src /\ plain_operand s len /\
        plain_operand s ibuf.buf_operand` >> simp[shape_stable_conj]) >>
  qx_gen_tac `dbuf` >> simp[] >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  qx_gen_tac `init_dyn` >> suspend "loop_init"
QED

Resume abi_encode_shape_mutual[loop_init]:
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule shape_step_bind >>
  qexists `\l s. (plain_operand s dst /\ plain_operand s src /\ plain_operand s len /\
    plain_operand s ibuf.buf_operand /\ plain_operand s dbuf.buf_operand /\
    plain_operand s init_dyn) /\ compiler_label l` >> reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label >>
      rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `hdr` >> reverse (Cases_on `compiler_label hdr`)
  >- simp[shape_step_def] >> simp[] >> suspend "loop_labels"
QED

Resume abi_encode_shape_mutual[loop_labels]:
  irule shape_step_bind >>
  qexists `\l s. (plain_operand s dst /\ plain_operand s src /\ plain_operand s len /\
    plain_operand s ibuf.buf_operand /\ plain_operand s dbuf.buf_operand /\
    plain_operand s init_dyn) /\ compiler_label l /\ label_sfx "enc_dyn_body" l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label_sfx >>
      rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `body_lbl` >>
  reverse (Cases_on `compiler_label body_lbl /\ label_sfx "enc_dyn_body" body_lbl`)
  >- simp[shape_step_def] >> simp[] >>
  irule shape_step_bind >>
  qexists `\l s. (plain_operand s dst /\ plain_operand s src /\ plain_operand s len /\
    plain_operand s ibuf.buf_operand /\ plain_operand s dbuf.buf_operand /\
    plain_operand s init_dyn) /\ compiler_label l /\ label_sfx "enc_dyn_exit" l` >>
  reverse conj_tac
  >- (ho_match_mp_tac shape_step_fresh_label_sfx >>
      rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `exit_lbl` >>
  reverse (Cases_on `compiler_label exit_lbl /\ label_sfx "enc_dyn_exit" exit_lbl`)
  >- simp[shape_step_def] >> simp[] >>
  `exit_lbl <> body_lbl` by (irule label_sfx_distinct >>
    qexistsl [`"enc_dyn_exit"`, `"enc_dyn_body"`] >> simp[]) >> suspend "loop_header"
QED

Resume abi_encode_shape_mutual[loop_header]:
  irule abi_encode_jmp_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule abi_encode_new_block_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `index` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `cmp` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `test` >>
  irule abi_encode_jnz_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule abi_encode_new_block_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  suspend "loop_body"
QED

Resume abi_encode_shape_mutual[loop_body]:
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `idx` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `src_data` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `src_off` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `child_src` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `dst_data` >> suspend "loop_offsets"
QED

Resume abi_encode_shape_mutual[loop_offsets]:
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `head_off` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `head_pos` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `dyn_ofst` >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `child_dst` >>
  irule shape_step_bind >>
  qexists `\v s. (plain_operand s src /\ plain_operand s ibuf.buf_operand /\
    plain_operand s dbuf.buf_operand /\ plain_operand s idx /\
    plain_operand s head_pos /\ plain_operand s dyn_ofst) /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      first_x_assum (irule_at Any) >>
      qexists `\s. plain_operand s src /\ plain_operand s ibuf.buf_operand /\
        plain_operand s dbuf.buf_operand /\ plain_operand s idx /\
        plain_operand s head_pos /\ plain_operand s dyn_ofst` >>
      simp[] >> rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `child_len` >> BETA_TAC >> suspend "loop_store"
QED

Resume abi_encode_shape_mutual[loop_store]:
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `new_dyn` >>
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  qx_gen_tac `new_i` >> suspend "loop_tail"
QED

Resume abi_encode_shape_mutual[loop_tail]:
  irule abi_encode_void_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  conj_tac
  >- simp[lowered_inst_ok_def, mk_inst_def, raw_opcode_ok_def, inst_shape_ok_def,
      inst_jump_labels_ok_def, is_param_opcode_def, is_read0_opcode_def,
      label_positions_ok_def, is_terminator_def, plain_operand_def, is_label_operand_def] >>
  conj_tac >- simp[label_or_plain_def, plain_operand_def] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule abi_encode_jmp_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule abi_encode_new_block_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  gen_tac >>
  irule target_scalar_op_bind >> simp[GSYM CONJ_ASSOC, shape_stable_conj] >>
  reverse conj_tac >- (rw[shape_stable_def] >> metis_tac[plain_operand_mono]) >>
  gen_tac >> irule shape_step_conseq >> irule_at Any target_scalar_op_shape >>
  qexists `\s. T` >> simp[shape_stable_def]
QED

Finalise abi_encode_shape_mutual

Theorem abi_encode_to_buf_shape:
  shape_step F compiler_label
    (\s. plain_operand s dst /\ plain_operand s src)
    (compile_abi_encode_to_buf dst src info) (\v s. plain_operand s v)
Proof
  simp[abi_encode_shape_mutual]
QED

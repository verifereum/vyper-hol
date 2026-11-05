(* Opcode observations of the scalar encoder, independent of byte correctness. *)
Theory stmtSimLogEncodeFields
Ancestors
  stmtSimLogExecFields stmtSimLogEncodeLayout abiEncoderBytesCode
  abiEncoderMemberPhaseEffect abiEncoderComplexPrefix abiEncoderMemberCode
  abiEncoderChildCode abiEncoderChildSuffix abiDecoderArrayInit
  abiEncoderComplexCode abiEncoder emitHelperProps exprLoweringProps
  compileEnv emitHelper context venomInst words list rich_list arithmetic

Theorem log_encode_copy_safe:
  compile_abi_encode_to_buf dst src (AbiCopy n) st = (out,final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, log_encode_safe_opcode_def, mk_inst_def]
QED

Theorem log_encode_bytes_safe[local]:
  compile_abi_encode_to_buf dst src (AbiBytestring n) st = (out,final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  simp[Once compile_abi_encode_child_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND, log_encode_safe_opcode_def, mk_inst_def]
QED

Theorem log_encode_scalar_safe[local]:
  compile_abi_encode_to_buf dst src ei st = (out,final) /\ log_scalar_enc_info ei ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  rw[log_scalar_enc_info_def] >>
  metis_tac[log_encode_copy_safe, log_encode_bytes_safe]
QED

Theorem log_encode_safe_append:
  inst_extends st mid /\ inst_extends mid final /\
  same_blocks st mid /\ same_blocks mid final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st mid) /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts mid final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  metis_tac[inst_extends_trans, abi_decoder_emitted_every_append, same_blocks_def]
QED

Theorem log_encode_emit_safe:
  emit_op opc ops st = (out,final) /\ log_encode_safe_opcode opc ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem log_encode_child_prefix_safe[local]:
  abi_encode_child_prefix dst ho dp st = (ops,final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  strip_tac >> drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encoder_member_prefix_opcodes >>
  simp[same_blocks_def, EVERY_MEM, log_encode_safe_opcode_def] >> metis_tac[]
QED

Theorem log_encode_child_suffix_safe[local]:
  abi_encode_child_suffix head dp offset len st = (out,final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  strip_tac >> drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_member_suffix_opcodes >>
  simp[same_blocks_def, EVERY_MEM, log_encode_safe_opcode_def] >> metis_tac[]
QED

Theorem log_encode_child_safe[local]:
  compile_abi_encode_child dst src ei dyn ho dp st = (out,final) /\
  log_scalar_enc_info ei ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  Cases_on `dyn` >> strip_tac
  >- (drule abi_encode_dynamic_child_trace >> strip_tac >>
      drule_all log_encode_scalar_safe >> strip_tac >>
      drule log_encode_child_prefix_safe >> strip_tac >>
      drule log_encode_child_suffix_safe >> strip_tac >>
      metis_tac[log_encode_safe_append]) >>
  drule abi_encode_static_child_trace >> strip_tac >>
  drule_all log_encode_scalar_safe >> strip_tac >>
  drule log_encode_emit_safe >>
  (impl_tac >- simp[log_encode_safe_opcode_def]) >> strip_tac >>
  irule log_encode_safe_append >> qexists_tac `prepared` >> simp[]
QED

Theorem log_encode_members_safe[local]:
  !infos dst src so ho dp st out final.
  compile_abi_encode_complex_elems dst src infos so ho dp st = (out,final) /\
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  Induct >> rpt gen_tac
  >- simp[Once compile_abi_encode_child_def, comp_return_def,
      same_blocks_def, inst_extends_def, emitted_insts_def] >>
  PairCases_on `h` >> strip_tac >>
  drule abi_encoder_member_cons_trace >> strip_tac >>
  `log_scalar_enc_info h0 /\ EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos`
    by fs[] >>
  drule_all log_encode_child_safe >> strip_tac >>
  first_x_assum drule >> disch_then drule >> strip_tac >>
  drule log_encode_emit_safe >>
  (impl_tac >- simp[log_encode_safe_opcode_def]) >> strip_tac >>
  `inst_extends st child_end /\ same_blocks st child_end /\
   EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st child_end)` by
    (irule log_encode_safe_append >> qexists_tac `prepared` >> simp[]) >>
  irule log_encode_safe_append >> qexists_tac `child_end` >> simp[]
QED

Theorem log_encode_cursor_safe[local]:
  abi_encode_complex_prefix infos st = (dp,final) ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  simp[abi_encode_complex_prefix_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, log_encode_safe_opcode_def, mk_inst_def]
QED

Theorem log_encode_dynamic_safe:
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,final) /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos ==>
  inst_extends st final /\ same_blocks st final /\
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  strip_tac >> drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule_all log_encode_members_safe >> strip_tac >>
  drule log_encode_cursor_safe >> strip_tac >>
  drule log_encode_emit_safe >>
  (impl_tac >- simp[log_encode_safe_opcode_def]) >> strip_tac >>
  `inst_extends st middle /\ same_blocks st middle /\
   EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st middle)` by
    (irule log_encode_safe_append >> qexists_tac `prepared` >> simp[]) >>
  irule log_encode_safe_append >> qexists_tac `middle` >> simp[]
QED

Theorem log_scalar_encode_safe:
  compile_abi_encode_to_buf dst src ei st = (out,final) /\
  ((?n. ei = AbiCopy n) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  EVERY (\i. log_encode_safe_opcode i.inst_opcode) (emitted_insts st final)
Proof
  strip_tac
  >- (gvs[] >> drule log_encode_copy_safe >> simp[]) >>
  gvs[] >> drule_all log_encode_dynamic_safe >> simp[]
QED

Theorem log_scalar_encode_external:
  compile_abi_encode_to_buf dst src ei st = (out,final) /\
  ((?n. ei = AbiCopy n) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) /\
  run_inst_seq (emitted_insts st final) initial = OK actual ==>
  log_encode_external actual = log_encode_external initial
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all log_scalar_encode_safe >> strip_tac >>
  irule log_encode_run_external >> goal_assum (drule_at Any) >> simp[]
QED

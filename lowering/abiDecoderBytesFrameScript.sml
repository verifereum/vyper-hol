(* Bytes and String sequences write only their output and do not allocate. *)
Theory abiDecoderBytesFrame
Ancestors
  abiDecoderRange abiDecoderBytesBound abiDecoderGuards abiDecoderComposition
  abiDecoderBytes abiDecoderBytesTyped abiDecoderString abiDecoderVarSequence
  abiDecoderReservation abiDecoderTypedContract abiDecoderContract abiCanonicalBytes
  abiCanonicalHeadSize abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  valueEncoding vyperABI vyperValue contractABI
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem abi_decode_range_reentry_trace:
  compile_abi_decode_range_check src e hi st = ((),st') ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st') /\ inst_extends st st'
Proof
  strip_tac >> drule compile_abi_decode_range_check_shape >> strip_tac >>
  gvs[compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def,
       is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_decode_head_reentry_trace[local]:
  abi_decode_bytes_head src hi st = (head,st') ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st') /\ inst_extends st st'
Proof
  strip_tac >> drule abi_decode_bytes_head_shape >> strip_tac >>
  Cases_on `hi = Lit 0w`
  >- gvs[abi_decode_bytes_head_def, comp_return_def, emitted_insts_def] >>
  qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_head_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  drule abi_decode_range_reentry_trace >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, emitted_insts_def,
      inst_extends_def, DROP_LENGTH_APPEND, mk_inst_def] >>
  qpat_x_assum `_ = _ ++ [_] ++ _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def,
      is_terminator_def, is_alloca_op_def] >>
  fs[abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_payload_reentry_trace[local]:
  abi_decode_bytes_payload_guard head len hi st = ((),st') ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st') /\ inst_extends st st'
Proof
  strip_tac >> drule abi_decode_bytes_payload_guard_shape >> strip_tac >>
  Cases_on `hi = Lit 0w`
  >- gvs[abi_decode_bytes_payload_guard_def, comp_return_def, emitted_insts_def] >>
  qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_payload_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule abi_decode_range_reentry_trace >> strip_tac >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, emitted_insts_def,
      inst_extends_def, DROP_LENGTH_APPEND, mk_inst_def] >>
  qpat_x_assum `_ = _ ++ [_] ++ _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp_tac (srw_ss()) [DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def,
      is_terminator_def, is_alloca_op_def] >>
  fs[abi_decoder_reentry_opcode_def]
QED

Theorem abi_decode_count_reentry_trace[local]:
  abi_decode_count_guard opc src limit st = (count_op,st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st') /\ inst_extends st st'
Proof
  strip_tac >> drule abi_decode_count_guard_shape >> strip_tac >>
  gvs[abi_decode_source_opcode_def] >>
  gvs[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def,
      is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_decode_trace_trans[local]:
  inst_extends a b /\ inst_extends b c /\
  EVERY P (emitted_insts a b) /\ EVERY P (emitted_insts b c) ==>
  EVERY P (emitted_insts a c) /\ inst_extends a c
Proof
  strip_tac >>
  `emitted_insts a c = emitted_insts a b ++ emitted_insts b c` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  simp[] >> metis_tac[inst_extends_trans]
QED

Theorem abi_decoder_bytes_reentry_code:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> drule abi_decode_bytes_phases >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac abi_decode_head_reentry_trace >>
  drule_all abi_decode_count_reentry_trace >> strip_tac >>
  imp_res_tac abi_decode_payload_reentry_trace >>
  rename1 `emit_void (abi_decode_copy_opcode opc) ops c3 = ((),st')` >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts c3 st') /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts c3 st') /\ inst_extends c3 st'` by
    (imp_res_tac inst_extends_emit_void >>
     gvs[abi_decode_source_opcode_def] >>
     gvs[abi_decode_copy_opcode_def, emit_void_def, comp_bind_def,
         fresh_id_def, emit_def, emitted_insts_def, DROP_LENGTH_APPEND,
         abi_decoder_reentry_opcode_def, is_terminator_def,
         is_alloca_op_def, mk_inst_def]) >>
  qpat_x_assum `!src' n' hi' dst'. _` kall_tac >>
  metis_tac[abi_decode_trace_trans]
QED

Theorem abi_decoder_typed_bytes_sequence_frame:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_pre ce env (BaseT (BytesT (Dynamic n))) (BaseTV (BytesT (Dynamic n)))
    (DecBytestring n) (contractABI$BytesV bs) (vyperValue$BytesV bs)
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs)
      st' d (abi_decode_bytes_copy_size n) b cap s t /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all abi_decoder_typed_bytes_sequence >> strip_tac >>
  drule abi_decoder_bytes_pre_facts >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_load opc (n2w sb:bytes32) s = n2w (LENGTH bs)` by
    (irule canonical_bytes_count_load >> asm_simp_tac bool_ss []) >>
  drule_all abi_decode_bytes_sequence >> strip_tac >> gvs[Excl "enc_def"] >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  asm_simp_tac bool_ss []
QED

Theorem abi_decoder_typed_string_sequence_frame:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_pre ce env (BaseT (StringT n)) (BaseTV (StringT n))
    (DecBytestring n) (contractABI$BytesV bs) (StringV (MAP (CHR o w2n) bs))
    st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post (BaseTV (StringT n)) (StringV (MAP (CHR o w2n) bs))
      st' d (type_memory_bytes ce (BaseT (StringT n))) b cap s t /\
    abi_decode_frame d (type_memory_bytes ce (BaseT (StringT n))) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all abi_decoder_typed_string_sequence >> strip_tac >>
  drule abi_decoder_string_pre_bytes >> strip_tac >>
  drule_all abi_decoder_typed_bytes_sequence_frame >> strip_tac >>
  qexists_tac `t` >>
  gvs[abi_decoder_string_post_bytes, abi_decode_bytes_copy_size_def, type_memory_bytes_def,
    Excl "enc_def"]
QED

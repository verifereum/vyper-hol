(* Bytes and String sequences write only their output and do not allocate. *)
Theory abiDecoderBytesFrame
Ancestors
  abiDecoderBytes abiDecoderBytesTyped abiDecoderString abiDecoderVarSequence
  abiDecoderReservation abiDecoderTypedContract abiDecoderContract abiCanonicalBytes
  abiCanonicalHeadSize abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  valueEncoding vyperABI vyperValue contractABI
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem abi_decoder_bytes_reentry_code:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc ==>
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (emitted_insts st st') /\
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  gvs[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    emit_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, abi_decoder_reentry_opcode_def,
    is_terminator_def, is_alloca_op_def, mk_inst_def]
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

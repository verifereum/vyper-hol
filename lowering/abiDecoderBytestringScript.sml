(* Coherent bytestring descriptors cover both Bytes and String. Their wrapped
   decoder executes the actual singleton prefix and child, for every source opcode. *)
Theory abiDecoderBytestring
Ancestors
  abiDecoderString abiDecoderPointed abiDecoderSingletonFragment
  abiDecoderBytestringCases abiDecoderCoherence abiDecoderTypedContract abiDecoderBytesTyped abiDecoderBytes
  abiDecoderTypedCompose abiDecoderDynamic abiEncoder exprLowering compileEnv
  vyperABI vyperTyping contractABI valueEncoding fragExec combin


Theorem abi_decoder_typed_bytestring_from_state:
  compile_abi_decode_to_buf dst src opc base_op hi (DecBytestring n) st = ((),st') /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_decoder_recursive_pre ce env sf ty tv (DecBytestring n) av v
    st last src dst opc base_op hi B sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post tv v st' d (type_memory_bytes ce ty) b cap initial) (K F)
Proof
  strip_tac >>
  qhdtm_assum `abi_decoder_recursive_pre`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_bytestring_cases >> disch_then (qspec_then `n` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >> gvs[] >>
  qhdtm_assum `abi_decoder_pre`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_pre_def]) >>
  Cases_on `av` >>
  gvs[abi_decoder_metadata_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
      has_type_def, abi_to_vyper_def, AllCaseEqs()] >>
  fs[type_to_abi_dec_info_def] >>
  FIRST [
    drule abi_decoder_typed_bytes_from_state >>
      simp[abi_decode_bytes_copy_size_def, type_memory_bytes_def] >>
      disch_then drule >> simp[],
    drule abi_decoder_typed_string_from_state >> simp[] >>
      disch_then drule >> simp[]]
QED

Theorem abi_decoder_wrapped_bytestring_from_state:
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  (base_op = Lit 0w \/ opc = MLOAD) /\
  compile_abi_decode_to_buf dst src opc base_op hi
    (DecComplex T [(DecBytestring n,32,mem_sz)]) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex T [(DecBytestring n,32,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc base_op hi B sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post tv v st' d (type_memory_bytes ce ty) b cap initial) (K F)
Proof
  strip_tac >>
  qpat_assum `type_to_abi_dec_info sf ce ty = _` (fn th =>
    qhdtm_x_assum `compile_abi_decode_to_buf` (assume_tac o REWRITE_RULE [GSYM th]) >>
    qhdtm_x_assum `abi_decoder_recursive_pre` (assume_tac o REWRITE_RULE [GSYM th])) >>
  irule (SIMP_RULE bool_ss [abi_decoder_singleton_post_function]
    abi_decoder_offset_singleton_fragment) >>
  asm_rewrite_tac [] >>
  goal_assum (drule_at Any) >>
  asm_simp_tac (srw_ss()) [dec_info_needs_offset_def] >> rpt strip_tac >> rfs[] >>
  `compile_abi_decode_to_buf child_dst child_src opc base_op hi (DecBytestring n)
     middle = ((),st')` by
    (irule abi_decoder_offset_singleton_child_compile >>
     conj_tac >- simp[dec_info_needs_offset_def] >>
     qexistsl_tac [`dst`, `mem_sz`, `src`, `st`] >> simp[]) >>
  fs[] >> drule abi_decoder_typed_bytestring_from_state >> simp[] >>
  disch_then drule >> simp[]
QED

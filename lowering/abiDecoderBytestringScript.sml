(* Coherent bytestring descriptors cover both Bytes and String. Their wrapped
   decoder executes the actual singleton prefix and child, for every source opcode. *)
Theory abiDecoderBytestring
Ancestors
  abiDecoderString abiDecoderPointed abiDecoderSingletonFragment
  abiDecoderCoherence abiDecoderTypedContract abiDecoderBytesTyped abiDecoderBytes
  abiDecoderTypedCompose abiDecoderDynamic abiEncoder exprLowering compileEnv
  vyperABI vyperTyping contractABI valueEncoding fragExec combin

Theorem abi_decoder_bytestring_cases:
  !ce env sf ty tv. abi_decoder_coherent ce env sf ty tv ==>
  !n. type_to_abi_dec_info sf ce ty = DecBytestring n ==>
  (ty = BaseT (BytesT (Dynamic n)) /\ tv = BaseTV (BytesT (Dynamic n))) \/
  (ty = BaseT (StringT n) /\ tv = BaseTV (StringT n))
Proof
  ho_match_mp_tac abi_decoder_coherent_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> gen_tac >> Cases_on `bt` >>
      FIRST [(rename1 `BytesT bd` >> Cases_on `bd`), all_tac] >>
      simp[Once type_to_abi_dec_info_def])
  >- simp[Once type_to_abi_dec_info_def]
  >- (rpt gen_tac >> strip_tac >> Cases_on `bound` >>
      simp[Once type_to_abi_dec_info_def])
  >- (rpt gen_tac >> strip_tac >> simp[Once type_to_abi_dec_info_def]) >>
  rpt gen_tac >> strip_tac >> simp[Once type_to_abi_dec_info_def]
QED

Theorem abi_decoder_typed_bytestring_from_state:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf ty tv (DecBytestring n) av v
    st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post tv v st' d (type_memory_bytes ce ty) b cap initial) (K F)
Proof
  strip_tac >>
  qpat_assum `abi_decoder_recursive_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_recursive_pre_def]) >>
  drule abi_decoder_bytestring_cases >> disch_then (qspec_then `n` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >> gvs[] >>
  qpat_assum `abi_decoder_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_pre_def]) >>
  Cases_on `av` >>
  gvs[abi_decoder_metadata_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
      has_type_def, abi_to_vyper_def, AllCaseEqs()] >>
  fs[type_to_abi_dec_info_def] >>
  FIRST [
    drule_all abi_decoder_typed_bytes_from_state >>
      simp[abi_decode_bytes_copy_size_def, type_memory_bytes_def],
    drule_all abi_decoder_typed_string_from_state >> simp[]]
QED

Theorem abi_decoder_wrapped_bytestring_from_state:
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  compile_abi_decode_to_buf dst src opc hi
    (DecComplex T [(DecBytestring n,32,mem_sz)]) st = ((),st') /\
  abi_decoder_recursive_pre ce env sf (TupleT [ty]) (TupleTV [tv])
    (DecComplex T [(DecBytestring n,32,mem_sz)])
    (ListV [av]) (ArrayV (TupleV [v])) st last src dst opc hi sb d b cap initial ==>
  frag_exec ctx st st' (\s. s = initial)
    (abi_decoder_post tv v st' d (type_memory_bytes ce ty) b cap initial) (K F)
Proof
  strip_tac >>
  irule (SIMP_RULE bool_ss [abi_decoder_singleton_post_function]
    abi_decoder_offset_singleton_fragment) >>
  qexistsl_tac [`av`, `dst`, `env`, `hi`, `last`, `mem_sz`, `opc`, `sb`, `sf`, `src`] >>
  asm_simp_tac (srw_ss()) [dec_info_needs_offset_def] >> rpt strip_tac >>
  `compile_abi_decode_to_buf child_dst child_src opc hi (DecBytestring n)
     middle = ((),st')` by
    (irule abi_decoder_offset_singleton_child_compile >>
     conj_tac >- simp[dec_info_needs_offset_def] >>
     qexistsl_tac [`dst`, `mem_sz`, `src`, `st`] >> simp[]) >>
  drule_all abi_decoder_typed_bytestring_from_state >> simp[]
QED

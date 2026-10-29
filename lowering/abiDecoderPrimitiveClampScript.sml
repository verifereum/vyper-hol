(* Canonical typed words satisfy every primitive decoder validation check. *)
Theory abiDecoderPrimitiveClamp
Ancestors
  abiDecoderSigned abiDecoderFixedBytes abiDecoderNumericWord abiDecoderClampedTyped
  abiDecoderWordTyped abiDecoderClamp abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract exprLowering compileEnv vyperABI vyperTyping valueEncoding venomState
  contractABI words

Theorem abi_decoder_int_metadata_clamp:
  abi_decoder_metadata ce env (BaseT (IntT bits)) (BaseTV (IntT bits)) root_di av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (Int bits) av ==>
  abi_decoder_clamp_valid (type_to_abi_clamp (BaseT (IntT bits)))
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  Cases_on `av` >> simp[abi_decoder_metadata_def, has_type_def] >> rpt strip_tac >>
  gvs[abi_to_vyper_def, check_IntV_def, AllCaseEqs()] >>
  drule_all (SIMP_RULE (srw_ss()) [] abi_decoder_canonical_int_clamp) >> simp[]
QED

Theorem abi_decoder_decimal_metadata_clamp:
  abi_decoder_metadata ce env (BaseT DecimalT) (BaseTV DecimalT) root_di av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (Int 168) av ==>
  abi_decoder_clamp_valid (type_to_abi_clamp (BaseT DecimalT))
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  Cases_on `av` >> simp[abi_decoder_metadata_def, has_type_def] >> rpt strip_tac >>
  gvs[abi_to_vyper_def, check_IntV_def, AllCaseEqs()] >>
  drule_all (SIMP_RULE (srw_ss()) [] abi_decoder_canonical_decimal_clamp) >>
  simp[type_to_abi_clamp_def]
QED

Theorem abi_decoder_base_word_info:
  is_word_type (BaseT bt) ==>
  type_to_abi_dec_info sf ce (BaseT bt) =
    DecPrimWord (type_to_abi_clamp (BaseT bt))
Proof
  Cases_on `bt` >>
  FIRST [rename1 `BytesT bound` >> Cases_on `bound`, all_tac] >>
  simp[is_word_type_def, Once type_to_abi_dec_info_def]
QED

Theorem abi_decoder_base_word_clamp:
  is_word_type (BaseT bt) /\
  abi_decoder_metadata ce env (BaseT bt) (BaseTV bt) root_di av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (vyper_base_to_abi_type bt) av ==>
  abi_decoder_clamp_valid (type_to_abi_clamp (BaseT bt))
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  strip_tac >>
  qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
  Cases_on `bt` >> gvs[is_word_type_def] >> FIRST
    [drule_all abi_decoder_canonical_uint_clamp >> simp[],
     drule_all abi_decoder_int_metadata_clamp >> simp[],
     drule_all abi_decoder_canonical_bool_clamp >> simp[type_to_abi_clamp_def],
     drule_all abi_decoder_decimal_metadata_clamp >> simp[],
     drule_all abi_decoder_canonical_address_clamp >> simp[type_to_abi_clamp_def],
     (rename1 `abi_decoder_metadata ce env (BaseT (BytesT bound)) _ _ _ _` >>
      Cases_on `bound` >> gvs[is_word_type_def] >>
      drule_all abi_decoder_canonical_fixed_bytes_clamp >> simp[])]
QED

Theorem abi_decoder_primitive_clamp:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  abi_decoder_metadata ce env ty tv root_di av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (vyper_to_abi_type env ty) av ==>
  abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  strip_tac >>
  drule abi_decoder_primitive_cases >> disch_then (qspec_then `clamp` mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >> gvs[]
  >- (rename1 `is_word_type (BaseT bt)` >>
      `type_to_abi_dec_info sf ce (BaseT bt) =
         DecPrimWord (type_to_abi_clamp (BaseT bt))` by
        (irule abi_decoder_base_word_info >> simp[]) >> gvs[] >>
      drule_all abi_decoder_base_word_clamp >> simp[]) >>
  gvs[Once type_to_abi_dec_info_def] >>
  drule_all (SIMP_RULE (srw_ss()) [] abi_decoder_canonical_flag_clamp) >> simp[]
QED

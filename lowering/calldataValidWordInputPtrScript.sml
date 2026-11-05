Theory calldataValidWordInputPtr
Ancestors
  abiDecoderValidContract abiDecoderPrimitiveCaller abiDecoderWordTyped
  abiDecoderCoherence abiDecoderTypedContract abiDecoderLayout abiDecodeRanges
  abiValidStatic vyperABIValid abiCanonicalHeadSize abiDecoderWordCopy
  valueEncodingProps valueEncoding venomState words list arithmetic

(* A primitive source-valid window is canonical even when bs has trailing bytes.
   This is an observation on the original state, with no execution resources. *)
Theorem abi_decoder_valid_primitive_source:
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst opc hi sb d b cap s /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (dec (vyper_to_abi_type env ty) bs) v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) =
    enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs) /\
  type_memory_bytes ce ty = 32
Proof
  pure_rewrite_tac [abi_decoder_valid_pre_def] >> strip_tac >>
  drule_all (cj 2 abi_decoder_primitive_cases) >> strip_tac >>
  drule_all (cj 3 abi_decoder_primitive_cases) >> strip_tac >>
  `abi_decoder_header ce env ty tv` by
    (drule abi_decoder_coherent_header >> simp[]) >>
  `~is_dynamic (vyper_to_abi_type env ty)` by
    fs[abi_decoder_header_def] >>
  `LENGTH (enc (vyper_to_abi_type env ty)
      (dec (vyper_to_abi_type env ty) bs)) = 32` by
    (qpat_assum `abi_decoder_metadata _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decoder_metadata_def]) >>
     drule_all abi_decoder_descended_encoding_length >> simp[]) >>
  `valid_enc (vyper_to_abi_type env ty) bs` by
    (irule vyper_decode_valid_enc_static >> simp[]) >>
  drule abi_static_prefix_static >> simp_tac bool_ss [abi_static_prefix_def] >>
  disch_then (qspec_then `bs` mp_tac) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  `32 <= LENGTH bs` by
    (fs[abi_decoder_header_def] >> decide_tac) >>
  `mem_bytes_at sb 32 (abi_decode_source opc s) = TAKE 32 bs` by
    (qspecl_then [`sb`, `0`, `32`, `LENGTH bs`, `abi_decode_source opc s`]
      mp_tac mem_bytes_at_window >> simp[]) >>
  `sb < dimword (:256)` by
    (fs[abi_decoder_ranges_def] >> decide_tac) >>
  `static_length (vyper_to_abi_type env ty) = 32` by
    fs[abi_decoder_header_def] >>
  asm_simp_tac (srw_ss())
    [LENGTH_TAKE_EQ, TAKE_TAKE_MIN, Excl "dec_def", Excl "vyper_decode_valid_enc_def"]
QED

Theorem calldata_valid_primitive_clamp:
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst CALLDATALOAD hi sb d b cap s /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  abi_decoder_clamp_valid clamp (abi_decode_load CALLDATALOAD (n2w sb : bytes32) s)
Proof
  strip_tac >> drule_all abi_decoder_valid_primitive_source >> strip_tac >>
  drule_all abi_decoder_primitive_clamp >> disch_then ACCEPT_TAC
QED

Theorem calldata_valid_primitive_word_layout:
  abi_decoder_valid_pre ce env sf ty tv bs v st src dst CALLDATALOAD hi sb d b cap s /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  mem_word_at d mem = abi_decode_load CALLDATALOAD (n2w sb : bytes32) s ==>
  val_in_memory tv v d mem
Proof
  strip_tac >> drule_all abi_decoder_valid_primitive_source >> strip_tac >>
  `mload d (s with vs_memory := mem) =
     mload sb (s with vs_memory := abi_decode_source CALLDATALOAD s)` by
    (drule abi_decode_load_mload >>
     disch_then (qspecl_then [`s`, `CALLDATALOAD`] mp_tac) >>
     simp[GSYM mem_word_at_eq_mload]) >>
  drule mload_eq_mem_bytes_at_eq >> simp[] >> strip_tac >>
  irule abi_decoder_primitive_canonical_layout >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

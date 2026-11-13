Theory exprSimAbiDecodeChildBounds
Ancestors
  abiDecoderCoherence abiDecoderSourceFacts abiDecodeRanges
  exprLowering vyperABI contractABI words

Theorem abi_decode_scalar_member_head:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
  ~is_dynamic (vyper_to_abi_type env ty) /\
  abi_embedded_static_size ce.ce_struct_fields ty = 32
Proof
  strip_tac >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >>
  qpat_x_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
  simp[Once abi_decoder_coherent_cases] >> strip_tac >>
  gvs[type_to_abi_dec_info_def, abi_member_head_size_def,
      contractABITheory.is_dynamic_def, contractABITheory.static_length_def]
  >- (Cases_on `bt` >>
      gvs[type_to_abi_dec_info_def, vyper_base_to_abi_type_def,
          abi_member_head_size_def, contractABITheory.is_dynamic_def,
          contractABITheory.static_length_def] >>
      Cases_on `b` >>
      gvs[type_to_abi_dec_info_def, vyper_base_to_abi_type_def,
          abi_member_head_size_def, contractABITheory.is_dynamic_def,
          contractABITheory.static_length_def]) >>
  Cases_on `bound` >> gvs[type_to_abi_dec_info_def]
QED

Theorem abi_decode_scalar_child_readable:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  off + abi_embedded_static_size ce.ce_struct_fields ty <= heads /\
  pos + heads <= H /\ B + H < dimword (:256) ==>
  pos + off + 32 <= H /\
  w2n (n2w (pos+off):bytes32) = pos+off /\
  B + (pos+off) + 32 < dimword (:256)
Proof
  strip_tac >> drule_all abi_decode_scalar_member_head >> strip_tac >>
  `pos + off < dimword (:256)` by decide_tac >>
  simp[w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem abi_decode_scalar_root_readable:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
  pos + abi_embedded_static_size ce.ce_struct_fields ty <= H /\
  B + H < dimword (:256) ==>
  pos + 32 <= H /\ w2n (n2w pos:bytes32) = pos /\
  B + pos + 32 < dimword (:256)
Proof
  strip_tac >>
  drule_all abi_decode_scalar_member_head >> strip_tac >>
  `pos < dimword (:256)` by decide_tac >>
  simp[w2n_n2w, arithmeticTheory.LESS_MOD] >> decide_tac
QED

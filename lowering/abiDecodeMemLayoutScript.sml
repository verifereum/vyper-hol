(* Coherent descriptor heads cover the loads used by memory decoding. *)
Theory abiDecodeMemLayout
Ancestors
  abiDecoderWordTyped abiDecoderDynamic abiDecoderCoherence abiDecoderContract
  abiEncoder compileEnv contractABI abiDecodeRanges words arithmetic

Theorem abi_decode_mem_descriptor_head:
  abi_decoder_coherent ce env sf ty tv ==>
  (dec_info_needs_offset (type_to_abi_dec_info sf ce ty) ==>
    32 <= abi_embedded_static_size ce.ce_struct_fields ty) /\
  (!clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp ==>
    abi_embedded_static_size ce.ce_struct_fields ty = 32)
Proof
  strip_tac >> drule abi_decoder_coherent_header >> strip_tac >>
  drule abi_decoder_coherent_dynamic >> strip_tac >> conj_tac
  >- (strip_tac >>
      `abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by
        (Cases_on `type_to_abi_dec_info sf ce ty` >>
         gvs[dec_info_needs_offset_def, abi_decoder_dynamic_def]) >>
      gvs[abi_decoder_header_def, abi_member_head_size_def]) >>
  rpt strip_tac >> drule abi_decoder_primitive_cases >>
  disch_then (qspec_then `clamp` mp_tac) >> simp[] >> strip_tac >>
  gvs[abi_decoder_header_def, abi_member_head_size_def]
QED

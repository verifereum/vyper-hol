Theory exprSimAbiDecodeArrayBounds
Ancestors
  abiDecoderCoherence abiDecodeRanges compileEnv exprLowering
  arithmetic words

Theorem abi_decode_dynarray_embedded_product_bound:
  abi_size_bound sf (ArrayT ty (Dynamic maxn)) < dimword (:256) ==>
  !n. n <= maxn ==> n * abi_embedded_static_size sf ty < dimword (:256)
Proof
  simp_tac bool_ss [abi_size_bound_def] >> strip_tac >>
  gen_tac >> strip_tac >>
  `n * abi_embedded_static_size sf ty <=
   maxn * abi_embedded_static_size sf ty` by simp[] >>
  `maxn * abi_embedded_static_size sf ty <=
   maxn * (abi_embedded_static_size sf ty +
     (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0))` by simp[] >>
  decide_tac
QED

Theorem abi_decode_dynarray_coherent_product_bound:
  abi_decoder_coherent ce env sf ty tv /\
  abi_size_bound ce.ce_struct_fields (ArrayT ty (Dynamic maxn)) < dimword (:256) ==>
  abi_embedded_static_size ce.ce_struct_fields ty =
    abi_member_head_size (vyper_to_abi_type env ty) /\
  (!n. n <= maxn ==> n * abi_member_head_size (vyper_to_abi_type env ty) < dimword (:256))
Proof
  strip_tac >> drule abi_decoder_coherent_header >>
  simp_tac bool_ss [abi_decoder_header_def] >> strip_tac >>
  drule abi_decode_dynarray_embedded_product_bound >> asm_rewrite_tac []
QED

Theorem abi_decode_dynarray_descriptor_product_bound:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) atv /\
  abi_size_bound ce.ce_struct_fields (ArrayT ty (Dynamic maxn)) < dimword (:256) ==>
  type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_member_head_size (vyper_to_abi_type env ty)) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) maxn /\
  (!n. n <= maxn ==> n * abi_embedded_static_size ce.ce_struct_fields ty < dimword (:256)) /\
  (!n. n <= maxn ==> n * abi_member_head_size (vyper_to_abi_type env ty) < dimword (:256))
Proof
  simp_tac (srw_ss()) [abi_decoder_coherent_array_iff] >> strip_tac >>
  drule_all abi_decode_dynarray_coherent_product_bound >> strip_tac >>
  drule abi_decode_dynarray_embedded_product_bound >>
  asm_simp_tac bool_ss [type_to_abi_dec_info_def]
QED

Theory bodyFullAbiDecodeArrayPrepareCountStride
Ancestors
  exprSimAbiDecodeWidthBoundary abiDecoderCoherence vyperTypeSystem
  exprLowering compileEnv valueEncoding words arithmetic

(* The destination fits the full dynamic array, so the count-cut MUL fits
   independently of whether the subsequent payload range check succeeds. *)
Theorem abi_decode_array_prepare_count_stride:
  type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)) =
    DecDynArray child stride mem_sz dyn maxn /\
  abi_decoder_coherent ce env ce.ce_struct_fields
    (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  assignable_type env (ArrayT ty (Dynamic maxn)) /\
  d + type_memory_size (ArrayTV tv (Dynamic maxn)) <= output_base + output_cap /\
  output_base + output_cap < dimword (:256) /\
  c <= maxn ==>
  c * stride < dimword (:256) /\
  w2n ((n2w c : 256 word) * n2w stride) = c * stride
Proof
  strip_tac >>
  `abi_decoder_coherent ce env ce.ce_struct_fields ty tv` by
    fs[abi_decoder_coherent_array_iff] >>
  `assignable_type env ty` by fs[assignable_type_def] >>
  `stride = abi_embedded_static_size ce.ce_struct_fields ty /\
   mem_sz = type_memory_bytes ce ty` by fs[type_to_abi_dec_info_def] >>
  `type_memory_size tv = mem_sz` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `stride <= mem_sz` by metis_tac[abi_decode_embedded_head_le_memory] >>
  `c * stride <= maxn * mem_sz` by (irule LESS_MONO_MULT2 >> simp[]) >>
  `c * stride < dimword (:256)` by
    (gvs[type_memory_size_def] >> decide_tac) >>
  simp[IgnAsm `stride = _`, word_mul_n2w, LESS_MOD]
QED

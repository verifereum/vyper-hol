(* A discovered output prefix does not presuppose valid future ABI elements. *)
Theory extcallDecoderPrefixMemory
Ancestors
  abiDecoderArrayScratch abiDecoderFrame abiDecoderContract
  valueEncodingProps valueEncoding venomState words list arithmetic

Theorem extcall_decoder_prefix_advance:
  LENGTH ps = j /\
  all_have_type tv ps /\
  elems_in_memory ps (d+32) tv before.vs_memory /\
  mem_word_at d before.vs_memory = n2w c /\
  mem_bytes_at B H before.vs_memory = bs /\
  val_in_memory tv v (d+32+j*type_memory_size tv) after.vs_memory /\
  abi_decode_footprint_frame fp before after /\
  abi_footprint_disjoint d 32 fp /\
  abi_footprint_disjoint (d+32) (j*type_memory_size tv) fp /\
  abi_footprint_disjoint B H fp ==>
  elems_in_memory (ps++[v]) (d+32) tv after.vs_memory /\
  mem_word_at d after.vs_memory = n2w c /\
  mem_bytes_at B H after.vs_memory = bs
Proof
  strip_tac >>
  conj_tac >- (irule abi_decode_footprint_frame_append_element >> metis_tac[]) >>
  conj_tac
  >- (drule_all abi_decode_footprint_frame_mload >>
      simp[GSYM mem_word_at_eq_mload]) >>
  drule_all abi_decode_footprint_frame_slice >> simp[]
QED

(* Dynamic-array memory invariant over the actual source bytes. *)
Theory abiDecoderValidArrayMemory
Ancestors
  abiDecoderArrayInvariant abiValidMember abiCanonicalHeadSize abiCanonicalHeadSize abiDecodeRanges
  abiDecoderContract valueEncodingProps valueEncoding vyperABI vyperValue venomState words list
  rich_list arithmetic

Definition abi_decoder_valid_array_memory_def:
  abi_decoder_valid_array_memory opc bs tv vs sb d j s <=>
    j <= LENGTH vs /\ mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
    elems_in_memory (TAKE j vs) (d + 32) tv s.vs_memory /\
    mem_bytes_at sb (LENGTH bs)
      (abi_decode_source opc s) = bs
End

Theorem abi_decoder_valid_array_memory_init:
  mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
  mem_bytes_at sb (LENGTH bs)
    (abi_decode_source opc s) = bs ==>
  abi_decoder_valid_array_memory opc bs tv vs sb d 0 s
Proof
  simp[abi_decoder_valid_array_memory_def, val_in_memory_def, Excl "enc_def"]
QED

Theorem abi_decoder_valid_array_memory_exit:
  abi_decoder_valid_array_memory opc bs tv vs sb d (LENGTH vs) s ==>
  val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d s.vs_memory
Proof
  simp[abi_decoder_valid_array_memory_def, val_in_memory_dynarray, Excl "enc_def"]
QED

Theorem abi_decoder_valid_array_memory_update[simp]:
  abi_decoder_valid_array_memory opc bs tv vs sb d j (update_var name w s) <=>
  abi_decoder_valid_array_memory opc bs tv vs sb d j s
Proof
  simp[abi_decoder_valid_array_memory_def, update_var_def, abi_decode_source_def, Excl "enc_def"]
QED

Theorem abi_decoder_valid_array_memory_jump[simp]:
  abi_decoder_valid_array_memory opc bs tv vs sb d j (jump_to lbl s) <=>
  abi_decoder_valid_array_memory opc bs tv vs sb d j s
Proof
  simp[abi_decoder_valid_array_memory_def, jump_to_def, abi_decode_source_def, Excl "enc_def"]
QED

Theorem abi_decoder_valid_array_memory_count:
  abi_decoder_valid_array_memory opc bs tv vs sb d j s /\
  32 <= LENGTH bs /\ abi_head_word bs = LENGTH vs /\
  sb + LENGTH bs < dimword (:256) ==>
  abi_decode_load opc (n2w sb : bytes32) s = n2w (LENGTH vs)
Proof
  simp_tac bool_ss [abi_decoder_valid_array_memory_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `sb < dimword (:256)` by decide_tac >>
  `mem_bytes_at sb 32 (abi_decode_source opc s) = TAKE 32 bs` by
    (mp_tac (SIMP_RULE bool_ss [ADD_CLAUSES, DROP_0]
      (Q.INST [`off` |-> `0:num`, `n` |-> `32:num`] abi_decode_source_window)) >>
     asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_decode_load_bytes, abi_head_word_bytes]
QED

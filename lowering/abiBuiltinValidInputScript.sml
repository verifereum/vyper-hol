(* Source-success inputs for recursive builtin decoding over actual bytes. *)
Theory abiBuiltinValidInput
Ancestors
  abiDecoderReadableTypes abiDecoderValidContract abiBuiltinSource abiBuiltinDecodeSetup
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiValidAggregateHeads
  abiDecodeRanges vyperABIValid vyperABI contractABI compileEnv valueEncoding valueEncodingProps
  venomState words list

Theorem abi_decoder_source_readable_head:
  evaluate_abi_decode env ty bs = INL v /\ abi_decoder_readable_type env ty ==>
  abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs
Proof
  strip_tac >> drule evaluate_abi_decode_vyper_valid_enc >> strip_tac >>
  qpat_assum `vyper_valid_enc _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [vyper_valid_enc_window]) >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (`!elem. vyper_to_abi_type env ty <> Array (SOME 0) elem` by
        metis_tac[abi_decoder_readable_type_head] >>
      drule_all abi_valid_dynamic_head_min >> asm_simp_tac bool_ss [abi_member_head_size_def]) >>
  asm_simp_tac bool_ss [abi_member_head_size_def]
QED

Definition abi_builtin_valid_pre_def:
  abi_builtin_valid_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap s <=>
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
      (dec (vyper_to_abi_type env ty) bs) v /\
    vyper_decode_valid_enc (vyper_to_abi_type env ty) bs /\
    (is_dynamic (vyper_to_abi_type env ty) \/
      static_length (vyper_to_abi_type env ty) <= LENGTH bs) /\
    val_in_memory (BaseTV (BytesT (Dynamic (LENGTH bs)))) (vyperValue$BytesV bs) p s.vs_memory /\
    eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
    abi_builtin_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
      (LENGTH bs) p d b cap s
End

Theorem abi_builtin_valid_source:
  abi_builtin_valid_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap s ==>
  mload p s = n2w (LENGTH bs) /\ mem_bytes_at (p + 32) (LENGTH bs) s.vs_memory = bs
Proof
  simp_tac bool_ss [abi_builtin_valid_pre_def] >> strip_tac >>
  fs[val_in_memory_def, mem_word_at_eq_mload]
QED

Theorem abi_builtin_valid_pre_from_source:
  abi_decoder_coherent ce env sf ty tv /\
  evaluate_abi_decode env ty bs = INL v /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_builtin_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap s ==>
  abi_builtin_valid_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_source_metadata >> strip_tac >>
  drule evaluate_abi_decode_vyper_valid_enc >> strip_tac >>
  drule vyper_valid_enc_length_lower >> strip_tac >>
  asm_simp_tac bool_ss [abi_builtin_valid_pre_def] >>
  fs[vyper_valid_enc_def, val_in_memory_def, Excl "enc_def", Excl "dec_def", Excl "vyper_decode_valid_enc_def"]
QED

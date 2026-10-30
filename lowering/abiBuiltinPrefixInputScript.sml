(* Incoming actual Bytes may extend the canonical prefix consumed by the decoder. *)
Theory abiBuiltinPrefixInput
Ancestors
  abiBuiltinSource abiBuiltinCanonicalPre abiBuiltinDecodeSetup abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract abiCanonicalHeadSize valueEncoding valueEncodingProps
  vyperABI contractABI compileEnv venomState words list

Definition abi_builtin_prefix_pre_def:
  abi_builtin_prefix_pre ce env sf ty tv bs av v st first last data min_size max_size p d b cap s <=>
    abi_decoder_coherent ce env sf ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
    val_in_memory (BaseTV (BytesT (Dynamic (LENGTH bs)))) (vyperValue$BytesV bs) p s.vs_memory /\
    eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
    abi_builtin_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
      (LENGTH bs) p d b cap s /\
    LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH bs /\
    TAKE (LENGTH (enc (vyper_to_abi_type env ty) av)) bs = enc (vyper_to_abi_type env ty) av
End

Theorem abi_builtin_prefix_source:
  abi_builtin_prefix_pre ce env sf ty tv bs av v st first last data min_size max_size
    p d b cap s ==>
  mload p s = n2w (LENGTH bs) /\
  mem_bytes_at (p + 32) (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
    enc (vyper_to_abi_type env ty) av
Proof
  simp_tac bool_ss [abi_builtin_prefix_pre_def] >> strip_tac >>
  `mem_bytes_at (p + 32) (LENGTH bs) s.vs_memory = bs` by fs[val_in_memory_def] >>
  `mload p s = n2w (LENGTH bs)` by fs[val_in_memory_def, mem_word_at_eq_mload] >>
  qspecl_then [`p + 32`, `0`, `LENGTH (enc (vyper_to_abi_type env ty) av)`,
    `LENGTH bs`, `s.vs_memory`] mp_tac mem_bytes_at_window >>
  asm_simp_tac (srw_ss()) [val_in_memory_def, mem_word_at_eq_mload]
QED

Theorem abi_builtin_prefix_pre_from_source:
  abi_decoder_coherent ce env sf ty tv /\ evaluate_abi_decode env ty bs = INL v /\
  LENGTH (enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs)) <= LENGTH bs /\
  TAKE (LENGTH (enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs))) bs =
    enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_builtin_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap s ==>
  abi_builtin_prefix_pre ce env sf ty tv bs (dec (vyper_to_abi_type env ty) bs) v st
    first last data min_size max_size p d b cap s
Proof
  strip_tac >> drule_all abi_builtin_source_metadata >> strip_tac >>
  asm_simp_tac bool_ss [abi_builtin_prefix_pre_def] >> fs[val_in_memory_def]
QED

(* Establish bytes/string encoder input from typed source memory.
   The compiler descriptor and ABI type are the actual translation results. *)
Theory abiEncoderSourceInput
Ancestors
  abiEncoderInput exprLowering valueEncoding vyperABI vyperTyping vyperMisc
  contractABI words list arithmetic

Theorem abi_encoder_bytes_source_input:
  value_has_type (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) /\
  val_wf (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) sb mem /\
  n < dimword (:256) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (BaseT (BytesT (Dynamic n))))
    (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bs)
    sb (type_memory_size (BaseTV (BytesT (Dynamic n)))) mem /\
  vyper_to_abi env (BaseT (BytesT (Dynamic n))) (vyperValue$BytesV bs) =
    SOME (contractABI$BytesV bs)
Proof
  simp[abi_encoder_input_bytes_iff, type_to_abi_enc_info_def, vyper_to_abi_type_def,
    vyper_base_to_abi_type_def, vyper_to_abi_def, value_has_type_def, val_wf_def,
    val_in_memory_def, has_type_def, valid_length_def, LET_THM] >> decide_tac
QED

Theorem abi_encoder_string_source_input:
  value_has_type (BaseTV (StringT n)) (StringV text) /\
  val_wf (BaseTV (StringT n)) (StringV text) /\
  val_in_memory (BaseTV (StringT n)) (StringV text) sb mem /\
  n < dimword (:256) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (BaseT (StringT n)))
    (vyper_to_abi_type env (BaseT (StringT n))) (contractABI$BytesV (MAP (n2w o ORD) text))
    sb (type_memory_size (BaseTV (StringT n))) mem /\
  vyper_to_abi env (BaseT (StringT n)) (StringV text) =
    SOME (contractABI$BytesV (MAP (n2w o ORD) text))
Proof
  `n2w_o_ORD = (n2w o ORD):char -> word8` by simp[FUN_EQ_THM, n2w_o_ORD_def] >>
  simp[abi_encoder_input_bytes_iff, type_to_abi_enc_info_def, vyper_to_abi_type_def,
    vyper_base_to_abi_type_def, vyper_to_abi_def, value_has_type_def, val_wf_def,
    val_in_memory_def, has_type_def, valid_length_def, LET_THM,
    combinTheory.o_DEF] >> decide_tac
QED

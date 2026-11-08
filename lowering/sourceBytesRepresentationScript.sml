(* Forward source conversion for allocation-free bytes/string leaves. *)
Theory sourceBytesRepresentation
Ancestors abiDecoderBytestring abiDecoderString abiDecoderCoherence
  vyperABI vyperTyping vyperValue compileEnv valueEncoding exprLowering
  contractABI list abiDecoderBytes calldataTypedRobustPtr

Theorem coherent_source_bytes_representation:
  abi_decoder_coherent ce env sf ty tv /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av ==>
  ?bs. av = contractABI$BytesV bs /\ LENGTH bs <= n /\
    enc (vyper_to_abi_type env ty) av =
      enc (contractABI$Bytes NONE) (contractABI$BytesV bs) /\
    type_memory_bytes ce ty = abi_decode_bytes_copy_size n /\
    (!d mem. val_in_memory tv v d mem <=>
      val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) d mem)
Proof
  strip_tac >> drule abi_decoder_bytestring_cases >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  gvs[] >> Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_def, vyper_to_abi_base_def] >>
  simp[type_memory_bytes_def, abi_decode_bytes_copy_size_def,
       val_in_memory_def, enc_def, vyperMiscTheory.n2w_o_ORD_eq]
QED


Theory externalReturnSourceWindowProbe
Ancestors
  abiEncoderSourceProducer abiEncoderSourceWindow abiEncoderWindow abiEncoderOpenInput
  contractABI valueEncoding loweringPosts vyperABI vyperValue words list rich_list

Theorem return_source_window_probe:
  abi_enc_plan env ty ei /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
  val_in_memory tv v sb mem ==>
  ?ct rv. enc ct rv = enc (vyper_to_abi_type env ty) av /\
    abi_encoder_window_input ei ct rv sb (type_memory_size tv) mem
Proof
  strip_tac >> drule_all abi_encoder_source_window >>
  metis_tac[abi_encoder_open_input_window]
QED

Theorem return_zero_representative_probe:
  enc (Tuple []) (ListV []) = [] /\
  abi_encoder_window_input (AbiCopy 0) (Tuple []) (ListV []) sb 0 mem
Proof
  simp[abi_encoder_window_copy_iff, has_type_def, valid_length_def,
       enc_def, is_dynamic_def, static_length_def, mem_bytes_at_def, REV_DEF]
QED

Theorem return_bytes_actual_window_probe:
  abi_encoder_open_input (AbiBytestring maxlen) ct (BytesV bs) sb cap mem ==>
  abi_encoder_window_input (AbiBytestring maxlen) ct (BytesV bs)
    sb (32 + LENGTH bs) mem
Proof
  strip_tac >> drule abi_encoder_open_bytes_actual_window >> simp[]
QED

Theorem return_bytes_source_actual_probe:
  evaluate_type env (BaseT (BytesT (Dynamic n))) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (BytesT (Dynamic n))) v = SOME (BytesV bs) /\
  val_in_memory tv v sb mem ==>
  abi_encoder_window_input (AbiBytestring n) (Bytes NONE) (BytesV bs)
    sb (val_footprint tv v) mem
Proof
  strip_tac >> drule_all abi_encoder_open_bytes_source >>
  disch_then (mp_tac o MATCH_MP abi_encoder_open_bytes_actual_window) >> strip_tac >>
  Cases_on `v` >> gvs[evaluate_type_def, vyper_to_abi_def, val_footprint_def]
QED

Theorem return_string_source_actual_probe:
  evaluate_type env (BaseT (StringT n)) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (StringT n)) v = SOME (BytesV bs) /\
  val_in_memory tv v sb mem ==>
  abi_encoder_window_input (AbiBytestring n) String (BytesV bs)
    sb (val_footprint tv v) mem
Proof
  strip_tac >> drule_all abi_encoder_open_string_source >>
  disch_then (mp_tac o MATCH_MP abi_encoder_open_bytes_actual_window) >> strip_tac >>
  Cases_on `v` >> gvs[evaluate_type_def, vyper_to_abi_def, val_footprint_def]
QED

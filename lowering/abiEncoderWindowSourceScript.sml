(* Actual bytes/string source windows, retaining declared singleton layout. *)
Theory abiEncoderWindowSource
Ancestors
  abiEncoderWindow abiEncoderSourceWindow abiEncoderOpenInput exprSim
  vyperABI valueEncoding vyperTyping contractABI list arithmetic words

Theorem abi_encoder_window_bytes_source:
  evaluate_type env (BaseT (BytesT (Dynamic n))) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (BytesT (Dynamic n))) v = SOME (BytesV bs) /\
  val_in_memory tv v sb mem ==>
  abi_encoder_window_input (AbiBytestring n) (Bytes NONE) (BytesV bs)
    sb (32 + LENGTH bs) mem
Proof
  strip_tac >> irule abi_encoder_open_bytes_actual_window >>
  qexists_tac `type_memory_size tv` >> irule abi_encoder_open_bytes_source >>
  qexistsl_tac [`env`, `v`] >> simp[]
QED

Theorem abi_encoder_window_string_source:
  evaluate_type env (BaseT (StringT n)) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (StringT n)) v = SOME (BytesV bs) /\
  val_in_memory tv v sb mem ==>
  abi_encoder_window_input (AbiBytestring n) String (BytesV bs)
    sb (32 + LENGTH bs) mem
Proof
  strip_tac >> irule abi_encoder_open_bytes_actual_window >>
  qexists_tac `type_memory_size tv` >> irule abi_encoder_open_string_source >>
  qexistsl_tac [`env`, `v`] >> simp[]
QED

Theorem abi_encoder_window_bytes_singleton_source:
  evaluate_type env (BaseT (BytesT (Dynamic n))) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (BytesT (Dynamic n))) v = SOME (BytesV bs) /\
  val_in_memory tv v sb mem ==>
  abi_encoder_window_input
    (AbiComplex [(AbiBytestring n,32,type_memory_size tv,T)])
    (Tuple [Bytes NONE]) (ListV [BytesV bs]) sb (32 + LENGTH bs) mem
Proof
  strip_tac >> drule_all abi_encoder_open_bytes_source >>
  simp_tac (srw_ss()) [Once abi_encoder_open_input_cases] >> strip_tac >>
  irule abi_encoder_window_singleton_bytes >> gvs[has_type_def, LET_THM]
QED

Theorem abi_encoder_window_string_singleton_source:
  evaluate_type env (BaseT (StringT n)) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi env (BaseT (StringT n)) v = SOME (BytesV bs) /\
  val_in_memory tv v sb mem ==>
  abi_encoder_window_input
    (AbiComplex [(AbiBytestring n,32,type_memory_size tv,T)])
    (Tuple [String]) (ListV [BytesV bs]) sb (32 + LENGTH bs) mem
Proof
  strip_tac >> drule_all abi_encoder_open_string_source >>
  simp_tac (srw_ss()) [Once abi_encoder_open_input_cases] >> strip_tac >>
  irule abi_encoder_window_singleton_bytes >> gvs[has_type_def, LET_THM]
QED

Theorem abi_encoder_window_bytes_footprint:
  32 + LENGTH bs <= val_footprint (BaseTV (BytesT (Dynamic n)))
    (vyperValue$BytesV bs)
Proof
  simp[val_footprint_def, le_word_size_mul]
QED

Theorem abi_encoder_window_string_footprint:
  32 + LENGTH str <= val_footprint (BaseTV (StringT n)) (StringV str)
Proof
  simp[val_footprint_def, le_word_size_mul]
QED

Theorem abi_encoder_window_bytes_actual_bound:
  sb + val_footprint (BaseTV (BytesT (Dynamic n)))
    (vyperValue$BytesV bs) <= limit ==>
  sb + (32 + LENGTH bs) <= limit
Proof
  mp_tac abi_encoder_window_bytes_footprint >> decide_tac
QED

Theorem abi_encoder_window_string_actual_bound:
  sb + val_footprint (BaseTV (StringT n)) (StringV str) <= limit ==>
  sb + (32 + LENGTH str) <= limit
Proof
  mp_tac abi_encoder_window_string_footprint >> decide_tac
QED

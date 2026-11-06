(* Pure descriptor shape, kept independent of standalone builtin execution. *)
Theory abiDecoderBytesShape
Ancestors
  abiDecoderBytes abiEncoder exprLowering compileEnv vyperTyping vyperABI

Theorem abi_valid_bytes_lowering:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) ==>
  needs_external_call_wrap ty /\
  type_to_abi_dec_info sf ce ty = DecBytestring n /\
  type_to_abi_dec_info sf ce (TupleT [ty]) =
    DecComplex T [(DecBytestring n,32,abi_decode_bytes_copy_size n)] /\
  type_memory_bytes ce ty = abi_decode_bytes_copy_size n /\
  type_memory_bytes ce (TupleT [ty]) = abi_decode_bytes_copy_size n
Proof
  strip_tac >> gvs[needs_external_call_wrap_def, type_to_abi_dec_info_def,
    is_abi_dynamic_def, abi_embedded_static_size_def, type_memory_bytes_def,
    abi_decode_bytes_copy_size_def]
QED

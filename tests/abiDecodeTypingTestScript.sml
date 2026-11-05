Theory abiDecodeTypingTest
Ancestors
  vyperTypeSystem

(* Fixed bytes are stack words; the decoder consumes a memory buffer. *)
Theorem abi_decode_rejects_fixed_input:
  ~well_typed_type_builtin_args (AbiDecode F) (BaseT (UintT 256))
    [BaseT (BytesT (Fixed 32))]
Proof
  simp[well_typed_type_builtin_args_def]
QED

(* None and zero-width bytes have no matching ABI decoder value domain. *)
Theorem abi_decode_rejects_invalid_output_types:
  ~type_builtin_result_ok FEMPTY (AbiDecode F) NoneT NoneT [] /\
  ~type_builtin_result_ok FEMPTY (AbiDecode F)
    (TupleT [BaseT (BytesT (Fixed 0))])
    (TupleT [BaseT (BytesT (Fixed 0))]) [] /\
  ~type_builtin_result_ok FEMPTY (AbiDecode F)
    (ArrayT (BaseT (BytesT (Fixed 0))) (Dynamic 1))
    (ArrayT (BaseT (BytesT (Fixed 0))) (Dynamic 1)) []
Proof
  simp[type_builtin_result_ok_def, assignable_type_def,
       abi_decode_bytes_widths_def]
QED

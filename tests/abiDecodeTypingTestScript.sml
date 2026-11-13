Theory abiDecodeTypingTest
Ancestors
  vyperTypeSystem vyperABI
Libs
  cv_transLib wordsLib

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

(* The minimum input size counts a dynamic component as its 32-byte head
   offset, as Vyper does: (DynArray[uint256, 1][2], DynArray[uint256, 1][2])
   accepts 64 zero bytes (both arrays alias one empty tail) and rejects 63. *)
Theorem abi_decode_min_size_is_head_size:
  ISL (evaluate_abi_decode FEMPTY
         (TupleT [ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2);
                  ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2)])
         (REPLICATE 64 0w)) /\
  evaluate_abi_decode FEMPTY
    (TupleT [ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2);
             ArrayT (ArrayT (BaseT (UintT 256)) (Dynamic 1)) (Fixed 2)])
    (REPLICATE 63 0w) = INR "abi_decode invalid"
Proof
  CONV_TAC cv_eval
QED

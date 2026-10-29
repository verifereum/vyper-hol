(* Successful source Bytes/String decoding establishes the noncanonical input
   contract. No re-encoding equality or padding length is assumed. *)
Theory abiValidBytesSource
Ancestors
  abiValidBytes abiDecoderValidBytes abiDecoderBytes abiDecoderBytesTyped
  valueEncoding valueEncodingProps vyperABI vyperTypeABI vyperValue contractABI
  abiDecoderContract compileEnv venomState words list arithmetic

Theorem abi_valid_bytes_source_decode:
  evaluate_abi_decode env (BaseT (BytesT (Dynamic n))) bs = INL v ==>
  ?payload. v = vyperValue$BytesV payload /\ valid_enc (Bytes NONE) bs /\
    dec (Bytes NONE) bs = contractABI$BytesV payload /\ LENGTH payload <= n /\
    LENGTH bs <= abi_decode_bytes_copy_size n
Proof
  simp[evaluate_abi_decode_def, decode_abi_value_def, vyper_valid_enc_def,
    vyper_strict_enc_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    abi_to_vyper_def, compatible_bound_def, vyper_abi_size_bound_def,
    abi_decode_bytes_copy_size_def, ceil32_def, AllCaseEqs()]
QED

Theorem abi_valid_string_source_decode:
  evaluate_abi_decode env (BaseT (StringT n)) bs = INL v ==>
  ?payload. v = StringV (MAP (CHR o w2n) payload) /\ valid_enc String bs /\
    dec String bs = contractABI$BytesV payload /\ LENGTH payload <= n /\
    LENGTH bs <= abi_decode_bytes_copy_size n
Proof
  simp[evaluate_abi_decode_def, decode_abi_value_def, vyper_valid_enc_def,
    vyper_strict_enc_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    abi_to_vyper_def, vyper_abi_size_bound_def,
    abi_decode_bytes_copy_size_def, ceil32_def, AllCaseEqs()]
QED

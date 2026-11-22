(* Branch confinement for the production ABI value and payload encoders. *)
Theory createSizeEncodeCode
Ancestors
  createSizeEncodeRowsCode createSizeEncodeCoreCode
  createSizeLocationCode createSizeTypedCopyCode

Theorem create_encode_values_cut_code:
  create_cut_code {} a (SND (compile_abi_encode_values_to_buf ce dst rows a))
Proof
  irule create_encode_values_case >>
  simp[create_unwrap_cut_code, create_store_memory_cut_code,
       create_encode_to_buf_cut_code]
QED

Theorem create_encode_payload_cut_code:
  create_cut_code {} a (SND (compile_abi_encode_payload ce single vals tys dst a))
Proof
  irule create_encode_payload_case >>
  simp[create_unwrap_cut_code, create_store_memory_cut_code,
       create_encode_to_buf_cut_code]
QED

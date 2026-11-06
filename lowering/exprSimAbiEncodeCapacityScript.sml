Theory exprSimAbiEncodeCapacity
Ancestors
  exprSimAbiEncodeSourceMetadata abiEncodeEndpointMetadata
  createMemoryInterface exprSimHypsDefs words arithmetic

Theorem abi_encode_nonword_output_representable:
  expr_body_pre ce cx env
    (TypeBuiltin ann (AbiEncode F mid) ty [e]) es ==>
  32 + 32 * word_size
    (abi_size_bound ce.ce_struct_fields (expr_type e) +
     (case mid of NONE => 0 | SOME _ => 4)) < dimword (:256)
Proof
  strip_tac >> drule abi_encode_endpoint_output_size >> simp[] >>
  simp[dimword_def] >> decide_tac
QED

Theorem abi_encode_nonword_length_bound:
  expr_body_pre ce cx env e es /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av ==>
  LENGTH (enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av) <=
    abi_size_bound ce.ce_struct_fields (expr_type e)
Proof
  metis_tac[abi_encode_body_evaluated_metadata, create_ctor_encoding_bound]
QED

(* Constructor probes for the semantic caller interface. *)
Theory externalReturnSemanticProbe
Ancestors
  abiEncoderWindow abiEncoderInput valueEncoding vyperValue
  contractABI e2eDefs vyperABI list arithmetic

Theorem return_dynamic_bytes_window:
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) sb mem /\
  has_type (Bytes NONE) (contractABI$BytesV bs) /\ LENGTH bs <= n ==>
  abi_encoder_window_input (AbiBytestring n) (Bytes NONE)
    (contractABI$BytesV bs) sb (32 + LENGTH bs) mem
Proof
  strip_tac >> irule window_bytes >>
  gvs[val_in_memory_def]
QED

Theorem return_singleton_window:
  abi_encoder_window_input ei at av sb cap mem /\ cap <= msz ==>
  abi_encoder_window_input
    (AbiComplex [(ei,abi_member_head_size at,msz,is_dynamic at)])
    (Tuple [at]) (ListV [av]) sb cap mem
Proof
  strip_tac >> irule window_complex >> qexists_tac `[at]` >>
  simp[abi_encoder_tuple_type_def, abi_encoder_member_span_def] >>
  qexists_tac `cap` >> simp[]
QED

Theorem return_empty_window:
  abi_encoder_window_input (AbiComplex []) (Tuple []) (ListV []) sb 0 mem
Proof
  irule window_complex >> qexists_tac `[]` >>
  simp[abi_encoder_tuple_type_def]
QED

Theorem return_nested_empty_window:
  abi_encoder_window_input
    (AbiComplex [(AbiComplex [],abi_member_head_size (Tuple []),0,
                   is_dynamic (Tuple []))])
    (Tuple [Tuple []]) (ListV [ListV []]) sb 0 mem
Proof
  irule return_singleton_window >> simp[return_empty_window]
QED

Theorem return_dynamic_bytes_encoding:
  return_bytes tops (BaseT (BytesT (Dynamic n))) (vyperValue$BytesV bs)
    (enc (Tuple [Bytes NONE]) (ListV [contractABI$BytesV bs]))
Proof
  simp[return_bytes_def, vyper_to_abi_def, vyper_to_abi_base_def,
       vyper_to_abi_type_def, needs_external_call_wrap_def]
QED

Theorem return_static_empty_copy_window:
  abi_encoder_window_input (AbiCopy 0) (Tuple [Tuple []])
    (ListV [ListV []]) sb 0 mem
Proof
  irule window_copy >>
  simp[has_type_def, is_dynamic_def, static_length_def,
       mem_bytes_at_def, enc_def] >> CONV_TAC EVAL
QED

Theorem return_nested_empty_encoding:
  return_bytes tops (TupleT [TupleT []])
    (ArrayV (TupleV [ArrayV (TupleV [])]))
    (enc (Tuple [Tuple []]) (ListV [ListV []]))
Proof
  simp[return_bytes_def, vyper_to_abi_def, vyper_to_abi_type_def,
       needs_external_call_wrap_def] >> CONV_TAC EVAL
QED

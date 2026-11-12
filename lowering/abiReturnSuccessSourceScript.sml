(* Source return decoding at the raw capped payload boundary. *)
Theory abiReturnSuccessSource
Ancestors
  abiBuiltinSource abiDecoderValidContract vyperABI vyperABIValid
  abiDecoderCoherence list rich_list arithmetic

Theorem abi_return_source_capped_success:
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  rv = (if needs_external_call_wrap ty then ArrayV (TupleV [v]) else v) /\
  cap = vyper_abi_size_bound env rt /\
  evaluate_abi_decode_return env ty bs = INL v ==>
  evaluate_abi_decode env rt (TAKE cap bs) = INL rv
Proof
  strip_tac >>
  gvs[evaluate_abi_decode_return_def, AllCaseEqs()] >>
  gvs[evaluate_abi_decode_returndata_def, AllCaseEqs()] >>
  gvs[evaluate_abi_decode_def, vyper_valid_enc_def,
       vyper_valid_enc_returndata_def, vyper_strict_enc_def,
       LENGTH_TAKE_EQ]
QED

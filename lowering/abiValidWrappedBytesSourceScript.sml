(* Source conversion for valid, possibly noncanonical singleton Bytes/String. *)
Theory abiValidWrappedBytesSource
Ancestors
  abiValidSingletonBytes vyperABI vyperValue contractABI words list arithmetic

Theorem abi_valid_wrapped_bytes_source_decode:
  evaluate_abi_decode env (TupleT [BaseT (BytesT (Dynamic n))]) bs =
    INL (ArrayV (TupleV [v])) ==>
  ?payload. v = vyperValue$BytesV payload /\ valid_enc (Tuple [Bytes NONE]) bs /\
    dec (Tuple [Bytes NONE]) bs = ListV [contractABI$BytesV payload] /\ LENGTH payload <= n
Proof
  simp[evaluate_abi_decode_def, decode_abi_value_def, vyper_valid_enc_def,
    vyper_strict_enc_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    abi_to_vyper_def, compatible_bound_def, AllCaseEqs()]
QED

Theorem abi_valid_wrapped_string_source_decode:
  evaluate_abi_decode env (TupleT [BaseT (StringT n)]) bs =
    INL (ArrayV (TupleV [v])) ==>
  ?payload. v = StringV (MAP (CHR o w2n) payload) /\ valid_enc (Tuple [String]) bs /\
    dec (Tuple [String]) bs = ListV [contractABI$BytesV payload] /\ LENGTH payload <= n
Proof
  simp[evaluate_abi_decode_def, decode_abi_value_def, vyper_valid_enc_def,
    vyper_strict_enc_def, vyper_to_abi_type_def, vyper_base_to_abi_type_def,
    abi_to_vyper_def, AllCaseEqs()]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_WRAPPED_BYTES_SOURCE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid wrapped source not kernel closed: " ^ n)
  end) (DB.thms "abiValidWrappedBytesSource");

(* Public ABI builtin execution contracts.
   Encoder inputs describe the complete source representation. Decoder inputs
   describe a canonical, typed ABI encoding. Both contracts require explicit
   nonwrapping memory/allocator bounds and execute the complete emitted CFG.
   abiBuiltinFlatChecks disproves the former unqualified flat-list contracts. *)
Theory builtinAbiProps
Ancestors
  abiBuiltinEncodeRun abiBuiltinDecodeCorrect

Theorem lower_abi_encode_correct = lower_abi_encode_run

Theorem lower_abi_decode_correct = lower_abi_decode_canonical

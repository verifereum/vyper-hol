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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("BUILTIN_ABI_PROPS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin public contract not kernel closed: " ^ n)
  end) (DB.thms "builtinAbiProps");

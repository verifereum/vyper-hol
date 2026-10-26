(* Interpret the completed method prefix and recursive payload as source Bytes. *)
Theory abiBuiltinEncodeMethodValue
Ancestors
  abiBuiltinEncodeMethodReach abiEncoderMemory valueEncoding valueEncodingProps
  venomState words list arithmetic

Theorem abi_builtin_encode_method_value:
  mload p s = n2w (LENGTH bytes+4) /\
  mem_bytes_at (p+32) 4 s.vs_memory = abi_builtin_encode_method_bytes mid /\
  mem_bytes_at (p+36) (LENGTH bytes) s.vs_memory = bytes ==>
  mem_bytes_at (p+32) (4+LENGTH bytes) s.vs_memory = abi_builtin_encode_method_bytes mid ++ bytes /\
  val_in_memory (BaseTV (BytesT (Dynamic (maxlen+4))))
    (vyperValue$BytesV (abi_builtin_encode_method_bytes mid ++ bytes)) p s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at (p+32) (4+LENGTH bytes) s.vs_memory = abi_builtin_encode_method_bytes mid ++ bytes` by
    (ONCE_REWRITE_TAC [abi_encoder_mem_split] >> asm_simp_tac (srw_ss()) [GSYM ADD_ASSOC]) >>
  asm_simp_tac (srw_ss()) [val_in_memory_def, mem_word_at_eq_mload,
    abi_builtin_encode_method_bytes_length, ADD_COMM] >>
  first_assum (ACCEPT_TAC o SIMP_RULE (srw_ss()) [ADD_COMM])
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_ENCODE_METHOD_VALUE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin method-ID value not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinEncodeMethodValue");

(* Establish the existing builtin decoder input contract from actual checked
   construction. Canonical bytes and numerical allocator resources remain
   explicit until the separate resource-history proof establishes them. *)
Theory abiCallerBuiltinInput
Ancestors
  abiCallerCoherence abiBuiltinSourceInput abiBuiltinCanonicalPre
  compileVyper compileEnv valueEncoding vyperTypeSystem vyperValue
  vyperABI vyperContext contractABI venomState

Theorem abi_caller_source_metadata:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v ==>
  abi_decoder_metadata ce (type_env tops) ty tv
    (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (dec (vyper_to_abi_type (type_env tops) ty) bs) v
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (type_env tops)
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
      ce_struct_fields ty tv` by
    (irule abi_caller_coherent >> simp[] >> qexists_tac `in_deploy` >> simp[]) >>
  drule_all abi_builtin_source_metadata >> simp[]
QED

Theorem abi_caller_canonical_pre:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  evaluate_abi_decode (type_env tops) ty bs = INL v /\
  bs = enc (vyper_to_abi_type (type_env tops) ty)
    (dec (vyper_to_abi_type (type_env tops) ty) bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_builtin_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap s ==>
  abi_builtin_canonical_pre ce (type_env tops) ce.ce_struct_fields ty tv
    (dec (vyper_to_abi_type (type_env tops) ty) bs) v st
    first last data min_size max_size p d b cap s
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (type_env tops)
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
      ce_struct_fields ty tv` by
    (irule abi_caller_coherent >> simp[] >> qexists_tac `in_deploy` >> simp[]) >>
  drule_all abi_builtin_canonical_pre_from_source >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_BUILTIN_INPUT_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller builtin input not kernel closed: " ^ n)
  end) (DB.thms "abiCallerBuiltinInput");

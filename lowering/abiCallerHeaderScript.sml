(* Actual checked compiler construction supplies every decoder header fact.
   Semantic environments may have declarations removed during struct descent.
   No coherence, dynamic-tag or size agreement is assumed at the public API. *)
Theory abiCallerHeader
Ancestors
  abiCallerAbiShape abiCallerMemorySize abiCallerStaticMemory abiCallerTypeEnv
  abiDecoderCoherence abiDecodeRanges compileVyper compileEnv
  vyperContext vyperValue vyperABI contractABI

Theorem abi_caller_header_from_shape:
  evaluate_type env ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  abi_caller_abi_shape ce.ce_struct_fields env ty ==>
  abi_decoder_header ce env ty tv
Proof
  strip_tac >> Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
  gvs[abi_decoder_header_def, abi_caller_abi_shape_def,
      abi_embedded_static_size_def, abi_member_head_size_def] >>
  irule abi_caller_static_memory >> simp[]
QED

Theorem abi_caller_descended_abi_shape:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  env SUBMAP type_env tops /\ evaluate_type env ty = SOME tv ==>
  abi_caller_abi_shape
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans).ce_struct_fields env ty
Proof
  strip_tac >> drule_all abi_caller_type_submap >> strip_tac >>
  drule_all abi_caller_abi_type_submap >> strip_tac >>
  mp_tac (Q.INST [`tops` |-> `tops`, `ty` |-> `ty`,
    `in_deploy` |-> `in_deploy`, `tv` |-> `tv`,
    `vis` |-> `vis`, `mut` |-> `mut`, `func_name` |-> `func_name`,
    `fargs` |-> `fargs`, `ret_type` |-> `ret_type`,
    `code_stmts` |-> `code_stmts`, `use_trans` |-> `use_trans`]
      abi_caller_constructed_abi_shape) >>
  simp[abi_caller_abi_shape_def]
QED

Theorem abi_caller_header:
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  env SUBMAP type_env tops /\ evaluate_type env ty = SOME tv ==>
  abi_decoder_header
    (build_compile_env tops vis mut func_name fargs ret_type
      (code_stmts:stmt list) use_trans) env ty tv
Proof
  strip_tac >> drule_all abi_caller_descended_memory_size >> strip_tac >>
  drule_all abi_caller_descended_abi_shape >> strip_tac >>
  irule abi_caller_header_from_shape >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_CALLER_HEADER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI caller header not kernel closed: " ^ n)
  end) (DB.thms "abiCallerHeader");

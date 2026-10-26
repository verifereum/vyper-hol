(* The real allocator and initializer establish a complete static encoder input.
   No initial or final source-memory layout is assumed. *)
Theory abiEmptyProducer
Ancestors
  abiEmptyAllocate abiEmptyAllocateCode abiEmptySize abiEmptyInputLeaves abiEmptyEffect
  abiBuiltinAllocationState abiDecoderCoherence abiDecoderReentry abiCallerCoherence
  exprLoweringProps compileEnv builtinSimple exprLowering valueEncoding vyperABI
  compileVyper vyperTypeSystem vyperValue vyperContext
  venomState venomExecSemantics finite_map words list arithmetic

Theorem abi_empty_producer_operand_live:
  compile_builtin_empty_complex outsz length_only st = (buf,final) ==>
  abi_decoder_operand_live final.cs_next_var buf.buf_operand
Proof
  strip_tac >> drule abi_empty_complex_parts >> strip_tac >>
  rename1 `compile_alloc_buffer outsz st = (buf,allocated)` >>
  drule abi_empty_alloc_buffer_shape >> strip_tac >>
  drule abi_empty_initializer_shape >> strip_tac >>
  irule abi_decoder_operand_live_mono >> qexists_tac `allocated.cs_next_var` >> simp[]
QED

Theorem abi_empty_static_producer:
  abi_decoder_coherent ce env sf ty tv /\
  ~is_dynamic (vyper_to_abi_type env ty) /\
  has_type (vyper_to_abi_type env ty) (default_to_abi tv) /\
  compile_builtin_empty_complex (type_memory_bytes ce ty) F st = (buf,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,type_memory_bytes ce ty)) /\
  p+type_memory_bytes ce ty < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    eval_operand buf.buf_operand actual = SOME (n2w p) /\
    buf.buf_size = type_memory_bytes ce ty /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) (vyper_to_abi_type env ty)
      (default_to_abi tv) p (type_memory_bytes ce ty) actual.vs_memory /\
    abi_empty_effect st.cs_next_var p (type_memory_bytes ce ty) limit_st
      (abi_builtin_allocate_state st.cs_next_id (type_memory_bytes ce ty) initial) actual /\
    inst_extends st final
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `type_memory_bytes ce ty < dimword (:256)` by decide_tac >>
  drule abi_empty_round_coherent >> strip_tac >>
  mp_tac (Q.INST [`outsz` |-> `type_memory_bytes ce ty`, `length_only` |-> `F`]
    abi_empty_complex_execute) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >> gvs[] >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK actual` >>
  drule_all abi_empty_coherent_static_input >> strip_tac >>
  qexists_tac `actual` >> asm_rewrite_tac[]
QED

Theorem abi_empty_checked_static_producer:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ty /\ evaluate_type (type_env tops) ty = SOME tv /\
  ~is_dynamic (vyper_to_abi_type (type_env tops) ty) /\
  has_type (vyper_to_abi_type (type_env tops) ty) (default_to_abi tv) /\
  compile_builtin_empty_complex (type_memory_bytes ce ty) F st = (buf,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,type_memory_bytes ce ty)) /\
  p+type_memory_bytes ce ty < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    eval_operand buf.buf_operand actual = SOME (n2w p) /\ buf.buf_size = type_memory_bytes ce ty /\
    abi_encoder_input (type_to_abi_enc_info ce.ce_struct_fields ce ty)
      (vyper_to_abi_type (type_env tops) ty) (default_to_abi tv)
      p (type_memory_bytes ce ty) actual.vs_memory /\
    abi_empty_effect st.cs_next_var p (type_memory_bytes ce ty) limit_st
      (abi_builtin_allocate_state st.cs_next_id (type_memory_bytes ce ty) initial) actual /\
    inst_extends st final
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent
     (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
     (type_env tops)
     (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
       ce_struct_fields ty tv` by
    (irule abi_caller_coherent >> asm_rewrite_tac[] >>
     qexists_tac `in_deploy` >> asm_rewrite_tac[]) >>
  drule_all abi_empty_static_producer >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_PRODUCER_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI Empty producer not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyProducer");

(* The actual complex Empty dispatcher produces a complete recursive ABI input.
   Source memory contents are established by execution, not assumed. *)
Theory abiEmptyDispatch
Ancestors
  abiEmptyDefaultProducer abiEmptyProducer abiEmptyAllocateCode abiEmptyEffect
  abiBuiltinAllocationState abiDecoderCoherence abiDecoderReentry abiCallerCoherence
  abiEncoderInput compileEnv builtinSimple exprLowering exprLoweringProps context
  valueEncoding vyperABI compileVyper vyperTypeSystem vyperValue vyperContext
  venomState venomExecSemantics finite_map words list arithmetic

Theorem abi_empty_dispatch_code:
  ~is_word_type ret_ty /\
  compile_type_builtin_dispatch_body cfn ce vv_ty src_ty Empty ret_ty args st = (vv,final) ==>
  ?buf. compile_builtin_empty_complex (type_memory_bytes ce ret_ty)
    (is_bytestring_type ret_ty \/ (case ret_ty of ArrayT _ (Dynamic _) => T | _ => F))
    st = (buf,final) /\ vv = LocatedValue vv_ty (base_ptr buf)
Proof
  simp_tac bool_ss [Once compile_type_builtin_dispatch_body_def, LET_THM] >>
  rpt strip_tac >>
  Cases_on `compile_builtin_empty_complex (type_memory_bytes ce ret_ty)
    (is_bytestring_type ret_ty \/ (case ret_ty of ArrayT _ (Dynamic _) => T | _ => F)) st` >>
  gvs[AllCaseEqs()]
QED

Theorem abi_empty_dispatch_input:
  let length_only = (is_bytestring_type ret_ty \/
    (case ret_ty of ArrayT _ (Dynamic _) => T | _ => F)) in
  abi_decoder_coherent ce env sf ret_ty tv /\
  has_type (vyper_to_abi_type env ret_ty) (default_to_abi tv) /\ ~is_word_type ret_ty /\
  compile_type_builtin_dispatch_body cfn ce vv_ty src_ty Empty ret_ty args st = (vv,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,type_memory_bytes ce ret_ty)) /\
  type_memory_bytes ce ret_ty < dimword (:256) /\
  p+abi_empty_initialized_bytes (type_memory_bytes ce ret_ty) length_only < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w p) /\
    abi_decoder_operand_live final.cs_next_var (vv_operand vv) /\
    abi_encoder_input (type_to_abi_enc_info sf ce ret_ty) (vyper_to_abi_type env ret_ty)
      (default_to_abi tv) p (type_memory_bytes ce ret_ty) actual.vs_memory /\
    abi_empty_effect st.cs_next_var p
      (abi_empty_initialized_bytes (type_memory_bytes ce ret_ty) length_only) limit_st
      (abi_builtin_allocate_state st.cs_next_id (type_memory_bytes ce ret_ty) initial) actual /\
    inst_extends st final
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_empty_dispatch_code >> strip_tac >>
  drule abi_empty_producer_operand_live >> strip_tac >>
  mp_tac (Q.INST [`ty` |-> `ret_ty`, `length_only` |->
    `is_bytestring_type ret_ty \/ (case ret_ty of ArrayT _ (Dynamic _) => T | _ => F)`]
    abi_empty_default_producer) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  qexists_tac `actual` >> gvs[vv_operand_def, vv_location_def, base_ptr_def]
QED

Theorem abi_empty_checked_dispatch_input:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  let length_only = (is_bytestring_type ret_ty \/
    (case ret_ty of ArrayT _ (Dynamic _) => T | _ => F)) in
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ret_ty /\ evaluate_type (type_env tops) ret_ty = SOME tv /\
  has_type (vyper_to_abi_type (type_env tops) ret_ty) (default_to_abi tv) /\
  ~is_word_type ret_ty /\
  compile_type_builtin_dispatch_body cfn ce vv_ty src_ty Empty ret_ty args st = (vv,final) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,type_memory_bytes ce ret_ty)) /\
  type_memory_bytes ce ret_ty < dimword (:256) /\
  p+abi_empty_initialized_bytes (type_memory_bytes ce ret_ty) length_only < dimword (:256) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w p) /\
    abi_decoder_operand_live final.cs_next_var (vv_operand vv) /\
    abi_encoder_input (type_to_abi_enc_info ce.ce_struct_fields ce ret_ty)
      (vyper_to_abi_type (type_env tops) ret_ty) (default_to_abi tv)
      p (type_memory_bytes ce ret_ty) actual.vs_memory /\
    abi_empty_effect st.cs_next_var p
      (abi_empty_initialized_bytes (type_memory_bytes ce ret_ty) length_only) limit_st
      (abi_builtin_allocate_state st.cs_next_id (type_memory_bytes ce ret_ty) initial) actual /\
    inst_extends st final
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent
     (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
     (type_env tops)
     (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
       ce_struct_fields ret_ty tv` by
    (irule abi_caller_coherent >> asm_rewrite_tac[] >>
     qexists_tac `in_deploy` >> asm_rewrite_tac[]) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_empty_dispatch_input) >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_EMPTY_DISPATCH_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI Empty dispatch not kernel closed: " ^ n)
  end) (DB.thms "abiEmptyDispatch");

(* Source-success dispatch under actual checked compiler-environment construction.
   Physical input ownership and numeric resources remain explicit. *)
Theory abiScratchDecodeCaller
Ancestors
  abiBuiltinDecodeSetup abiScratchDecodeDispatch abiCallerCoherence abiDecoderReadableTypes
  abiBuiltinSource abiScratchDecodeEffect abiDecoderCoherence abiDecoderContract abiDecoderLoop
  abiDecoderReentry exprLowering builtinAbi fragExec compileVyper compileEnv context
  valueEncoding vyperTypeSystem vyperValue vyperABI vyperContext venomState words list

Theorem compile_abi_decode_memory_scratch_caller:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  let wrapped_ty = if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty in
  let min_size = abi_static_size ce.ce_struct_fields wrapped_ty in
  let max_size = abi_size_bound ce.ce_struct_fields wrapped_ty in
  get_tenv cx = type_env tops /\
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ret_ty /\
  evaluate_type (type_env tops) ret_ty = SOME tv /\
  evaluate_type_builtin cx (AbiDecode unwrap) ret_ty arg_tys [BytesV bs] = INL v /\
  cfn ce (expr_type (HD args)) (HD args) origin =
    (LocatedValue (BaseT (BytesT (Dynamic n))) srcptr,ready) /\
  srcptr.ptr_location = LocMemory /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiDecode unwrap) ret_ty args origin =
    (vv,final) /\ fn_has_code ready final func /\
  (ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) src_base prepared.vs_memory /\
  eval_operand srcptr.ptr_operand prepared = SOME (n2w src_base) /\
  abi_decoder_operand_live ready.cs_next_var srcptr.ptr_operand /\
  abi_scratch_decode_resources ready first last min_size max_size (type_memory_bytes ce ret_ty)
    (LENGTH bs) src_base d b cap prepared /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st prepared /\ ~prepared.vs_halted /\
  prepared.vs_current_bb = ready.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
  abi_decode_sim ctx func initial prepared ==>
  ?actual. vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w d) /\
    val_in_memory tv v d actual.vs_memory /\
    abi_scratch_decode_effect first last ready final limit_st
      (abi_builtin_decode_output_site ready min_size max_size) d (type_memory_bytes ce ret_ty)
      b cap prepared actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_coherent
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans)
    (get_tenv cx)
    (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).
      ce_struct_fields ret_ty tv` by
    (asm_simp_tac bool_ss [] >> irule abi_caller_coherent >> asm_simp_tac bool_ss [] >>
     qexists_tac `in_deploy` >> asm_simp_tac bool_ss []) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] compile_abi_decode_memory_scratch) >> simp[]
QED

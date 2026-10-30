Theory abiScratchDecodeHistoryCaller
Ancestors
  abiBuiltinDecodeSetup abiScratchDecodeDispatch abiCallerBuiltinInput abiDecoderReadableTypes
  abiBuiltinSource abiScratchDecodeEffect abiDecoderCoherence abiDecoderContract abiDecoderLoop
  abiDecoderReentry exprLowering builtinAbi fragExec compileVyper compileEnv context
  valueEncoding vyperTypeSystem vyperValue vyperABI vyperContext venomState words list
  abiAllocationHistory abiScratchDecodeInput abiCallerDecodeBounds abiBuiltinAllocation
  abiDecoderAllocation venomInst venomExecSemantics finite_map relation pred_set

(* Source-success dispatch under actual checked compiler-environment construction.
   Physical input ownership and numeric resources remain explicit. *)
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

(* TOP-LEVEL: checked source decoding from actual allocation history.
   The output site may be fresh or reused. Code-owned scratch sizes and finite
   numeric credit establish resources; no separation or coherence is assumed. *)
Theorem compile_abi_decode_memory_history_caller:
  let ce = build_compile_env tops vis mut func_name fargs ret_type
    (code_stmts:stmt list) use_trans in
  let wrapped_ty = if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty in
  let min_size = abi_static_size ce.ce_struct_fields wrapped_ty in
  let max_size = abi_size_bound ce.ce_struct_fields wrapped_ty in
  let outsz = type_memory_bytes ce ret_ty in
  let site = abi_builtin_decode_output_site ready min_size max_size in
  let allocated = abi_builtin_allocate_state site outsz prepared in
  let cap = allocated.vs_alloca_next + 32 * CARD (abi_decoder_missing first last allocated) in
  get_tenv cx = type_env tops /\
  contract_namespaces_ok in_deploy [((NONE:num option),tops)] /\
  assignable_type (type_env tops) ret_ty /\ evaluate_type (type_env tops) ret_ty = SOME tv /\
  evaluate_type_builtin cx (AbiDecode unwrap) ret_ty arg_tys [BytesV bs] = INL v /\
  cfn ce (expr_type (HD args)) (HD args) origin =
    (LocatedValue (BaseT (BytesT (Dynamic n))) srcptr,ready) /\ srcptr.ptr_location = LocMemory /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiDecode unwrap) ret_ty args origin =
    (vv,final) /\ fn_has_code ready final func /\
  (ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) p prepared.vs_memory /\
  eval_operand srcptr.ptr_operand prepared = SOME (n2w p) /\
  abi_decoder_operand_live ready.cs_next_var srcptr.ptr_operand /\
  RTC (\s t. ?fuel inst. MEM inst code /\ step_inst fuel ctx inst s = OK t) entry prepared /\
  entry.vs_allocas = FEMPTY /\
  (!inst. MEM inst code /\ inst.inst_id IN abi_decoder_ids first last /\
    inst.inst_opcode = ALLOCA ==> inst.inst_operands = [Lit 32w]) /\
  cap < dimword (:256) /\ max_size < dimword (:256) /\
  FLOOKUP prepared.vs_allocas source_id = SOME (source_base,source_cap) /\ source_id <> site /\
  source_base <= p /\ p+32+LENGTH bs <= source_base+source_cap /\
  ((FLOOKUP prepared.vs_allocas site = NONE /\ d = prepared.vs_alloca_next) \/
    FLOOKUP prepared.vs_allocas site = SOME (d,outsz)) /\
  site < first /\ first <= site+2 /\ ~(source_id IN abi_decoder_ids first last) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st prepared /\ ~prepared.vs_halted /\
  prepared.vs_current_bb = ready.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
  abi_decode_sim ctx func initial prepared ==>
  ?actual. vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w d) /\
    val_in_memory tv v d actual.vs_memory /\
    abi_scratch_decode_effect first last ready final limit_st site d outsz 0 cap prepared actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`ty` |-> `ret_ty`] abi_caller_source_decode_wrapped_bounds)) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`st` |-> `ready:compile_state`, `initial` |-> `prepared:venom_state`,
    `cnt` |-> `LENGTH (bs:word8 list)`,
    `min_size` |-> `abi_static_size
      (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty)`,
    `max_size` |-> `abi_size_bound
      (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans).ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty)`,
    `outsz` |-> `type_memory_bytes
      (build_compile_env tops vis mut func_name fargs ret_type code_stmts use_trans) ret_ty`]
    abi_alloca_history_decode_resources) >>
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`src_base` |-> `p:num`, `b` |-> `0:num`]
      compile_abi_decode_memory_scratch_caller)) >>
  simp[]
QED

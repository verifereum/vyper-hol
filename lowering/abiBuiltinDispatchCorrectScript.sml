(* Compose argument evaluation with the actual AbiDecode dispatcher branch.
   The argument callback supplies its usual execution relation and Bytes value;
   all emitted decode instructions are executed by the source correctness theorem. *)
Theory abiBuiltinDispatchCorrect
Ancestors
  abiBuiltinSource abiBuiltinDecodeEffect abiDecodeUnwrapCase abiDecoderCoherence
  abiDecoderContract abiDecoderLoop exprLowering builtinAbi fragExec compileEnv context
  valueEncoding vyperABI vyperContext contractABI venomState venomExecSemantics words list

Theorem as_ptr_val_result:
  as_ptr_val ty loc result = (vv,st) ==>
  ?op. result = (op,st) /\ vv = LocatedValue ty (mk_ptr op loc)
Proof
  Cases_on `result` >> simp[as_ptr_val_def]
QED

Theorem compile_abi_decode_memory_trace:
  cfn ce (expr_type (HD args)) (HD args) origin =
    (LocatedValue (BaseT (BytesT (Dynamic n))) srcptr,ready) /\
  srcptr.ptr_location = LocMemory /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiDecode unwrap) ret_ty args origin =
    (vv,final) ==>
  ?out. lower_abi_decode srcptr.ptr_operand
    (type_to_abi_dec_info ce.ce_struct_fields ce
      (if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty))
    (abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty))
    (abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty))
    (type_memory_bytes ce
      (if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty)) ready =
    (out,final) /\ vv = LocatedValue vv_ty (mk_ptr out LocMemory)
Proof
  strip_tac >>
  gvs[compile_type_builtin_dispatch_body_def, unwrap_value_def, is_word_type_def,
      comp_return_def, LET_THM] >>
  drule as_ptr_val_result >> simp[]
QED

Theorem compile_abi_decode_memory_canonical:
  let wrapped = (unwrap /\ needs_external_call_wrap ret_ty) in
  let wrapped_ty = if wrapped then TupleT [ret_ty] else ret_ty in
  let wrapped_tv = if wrapped then TupleTV [tv] else tv in
  let wrapped_v = if wrapped then ArrayV (TupleV [v]) else v in
  let min_size = abi_static_size ce.ce_struct_fields wrapped_ty in
  let max_size = abi_size_bound ce.ce_struct_fields wrapped_ty in
  cfn ce (expr_type (HD args)) (HD args) origin =
    (LocatedValue (BaseT (BytesT (Dynamic n))) srcptr,ready) /\
  srcptr.ptr_location = LocMemory /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiDecode unwrap) ret_ty args origin =
    (vv,final) /\ fn_has_code ready final func /\
  (ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce (get_tenv cx) ce.ce_struct_fields wrapped_ty wrapped_tv /\
  evaluate_abi_decode (get_tenv cx) wrapped_ty bs = INL wrapped_v /\
  bs = enc (vyper_to_abi_type (get_tenv cx) wrapped_ty)
    (dec (vyper_to_abi_type (get_tenv cx) wrapped_ty) bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) src_base prepared.vs_memory /\
  eval_operand srcptr.ptr_operand prepared = SOME (n2w src_base) /\
  abi_decoder_operand_live ready.cs_next_var srcptr.ptr_operand /\
  abi_builtin_decode_resources ready first last min_size max_size (type_memory_bytes ce wrapped_ty)
    (LENGTH bs) src_base d b cap prepared /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st prepared /\ ~prepared.vs_halted /\
  prepared.vs_current_bb = ready.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
  abi_decode_sim ctx func initial prepared ==>
  ?actual. evaluate_type_builtin cx (AbiDecode unwrap) ret_ty [BytesV bs] = INL v /\
    vv_location vv = SOME LocMemory /\ eval_operand (vv_operand vv) actual = SOME (n2w d) /\
    val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last ready final limit_st d (type_memory_bytes ce ret_ty)
      b cap prepared actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all compile_abi_decode_memory_trace >> strip_tac >>
  mp_tac (Q.INST [`ty` |-> `ret_ty`, `sf` |-> `ce.ce_struct_fields`,
    `data` |-> `srcptr.ptr_operand`, `start` |-> `ready`, `initial` |-> `prepared:venom_state`,
    `min_size` |-> `abi_static_size ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty)`,
    `max_size` |-> `abi_size_bound ce.ce_struct_fields
      (if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty)`]
    lower_abi_decode_source_canonical) >>
  simp_tac bool_ss [LET_THM] >> impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `val_in_memory tv v d actual.vs_memory` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [vv_location_def, vv_operand_def, mk_ptr_def] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

Theorem compile_abi_decode_memory_unwrap_true_canonical =
  SIMP_RULE bool_ss [LET_THM] (Q.INST [`unwrap` |-> `T`] compile_abi_decode_memory_canonical);

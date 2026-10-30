(* Actual source dispatcher composition for noncanonical Bytes/String decoding. *)
Theory abiValidBytesDispatch
Ancestors
  abiValidBytesUnwrap abiBuiltinDispatchCorrect abiBuiltinValidBytes abiDecoderContract
  abiDecoderLoop abiDecoderReentry exprLowering builtinAbi fragExec compileEnv context
  valueEncoding vyperABI vyperContext venomState words list

Theorem compile_abi_decode_memory_valid_bytes:
  let wrapped_ty = if unwrap /\ needs_external_call_wrap ret_ty then TupleT [ret_ty] else ret_ty in
  let min_size = abi_static_size ce.ce_struct_fields wrapped_ty in
  let max_size = abi_size_bound ce.ce_struct_fields wrapped_ty in
  (ret_ty = BaseT (BytesT (Dynamic n)) \/ ret_ty = BaseT (StringT n)) /\
  evaluate_type (get_tenv cx) ret_ty = SOME tv /\
  evaluate_type_builtin cx (AbiDecode unwrap) ret_ty arg_tys [BytesV bs] = INL v /\
  cfn ce (expr_type (HD args)) (HD args) origin =
    (LocatedValue (BaseT (BytesT (Dynamic input_bound))) srcptr,ready) /\
  srcptr.ptr_location = LocMemory /\
  compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiDecode unwrap) ret_ty args origin =
    (vv,final) /\ fn_has_code ready final func /\
  abi_builtin_valid_bytes_resources n bs ready srcptr.ptr_operand min_size max_size
    p d prepared /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = ready.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\
  abi_decode_sim ctx func initial prepared ==>
  ?actual. vv_location vv = SOME LocMemory /\
    eval_operand (vv_operand vv) actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_decode_frame d (type_memory_bytes ce ret_ty) prepared actual /\
    fresh_vars_wrt final actual /\
    (!op w. abi_decoder_operand_live ready.cs_next_var op /\ eval_operand op prepared = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all compile_abi_decode_memory_trace >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM] lower_abi_decode_valid_bytes_unwrap) >>
    disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [vv_location_def, vv_operand_def, mk_ptr_def] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

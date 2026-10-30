Theory abiValidBytesCaller
Ancestors
  abiValidBytesUnwrap abiBuiltinDispatchCorrect abiBuiltinValidBytes abiDecoderContract
  abiDecoderLoop abiDecoderReentry exprLowering builtinAbi fragExec compileEnv context
  valueEncoding vyperABI vyperContext venomState words list abiBuiltinDecodeSetup
  abiDecoderBytes abiDecoderBytesTyped vyperABIValid contractABI finite_map arithmetic

(* Actual source dispatcher composition for noncanonical Bytes/String decoding. *)
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

(* Source success establishes the actual builtin's minimum/maximum length guards. *)
Theorem abi_valid_bytes_decode_bounds:
  let wrapped_ty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  evaluate_type_builtin cx (AbiDecode unwrap) ty arg_tys [vyperValue$BytesV bs] = INL v ==>
  abi_static_size sf wrapped_ty <= LENGTH bs /\ LENGTH bs <= abi_size_bound sf wrapped_ty
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_x_assum `evaluate_type_builtin _ _ _ _ _ = _`
    (assume_tac o PURE_REWRITE_RULE [abi_source_decode_wrapping_iff]) >>
  drule_all evaluate_abi_decode_vyper_valid_enc >> strip_tac >>
  drule vyper_valid_enc_length_lower >> strip_tac >>
  drule vyper_valid_enc_length_upper >> strip_tac >>
  qpat_x_assum `evaluate_abi_decode _ _ _ = _` kall_tac >>
  qpat_x_assum `vyper_valid_enc _ _ _` kall_tac >>
  Cases_on `unwrap` >>
  gvs[needs_external_call_wrap_def, abi_static_size_def, abi_size_bound_def,
    is_abi_dynamic_def, abi_embedded_static_size_def, vyper_abi_size_bound_def,
    vyper_is_dynamic_def, vyper_to_abi_type_def,
    vyper_base_to_abi_type_def, static_length_def, ceil32_def]
QED

Theorem abi_valid_bytes_resources_from_source:
  let wrapped_ty = if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty in
  let min_size = abi_static_size sf wrapped_ty in
  let max_size = abi_size_bound sf wrapped_ty in
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) /\
  evaluate_type_builtin cx (AbiDecode unwrap) ty arg_tys [vyperValue$BytesV bs] = INL v /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  max_size < dimword (:256) /\
  p + 32 + LENGTH bs < dimword (:256) /\
  d + abi_decode_bytes_copy_size n < dimword (:256) /\ fresh_vars_wrt st s /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) =
      SOME (d,abi_decode_bytes_copy_size n)) ==>
  abi_builtin_valid_bytes_resources n bs st data min_size max_size p d s
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_valid_bytes_decode_bounds) >>
    disch_then (qspec_then `sf` strip_assume_tac) >>
  `n + 32 <= abi_decode_bytes_copy_size n` by
    (irule (cj 3 abi_decoder_bytes_copy_size)) >>
  `n < dimword (:256)` by decide_tac >>
  asm_simp_tac bool_ss [abi_builtin_valid_bytes_resources_def] >>
  fs[val_in_memory_def]
QED

(* Bytes/String source dispatch with semantic guards established, for both unwrap choices.
   Numeric address credit and the actual allocation-site history remain explicit. *)
Theorem compile_abi_decode_bytes_source_caller:
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
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (BytesV bs) p prepared.vs_memory /\
  eval_operand srcptr.ptr_operand prepared = SOME (n2w p) /\
  abi_decoder_operand_live ready.cs_next_var srcptr.ptr_operand /\
  max_size < dimword (:256) /\ p + 32 + LENGTH bs < dimword (:256) /\
  d + abi_decode_bytes_copy_size n < dimword (:256) /\ fresh_vars_wrt ready prepared /\
  ((FLOOKUP prepared.vs_allocas (abi_builtin_decode_output_site ready min_size max_size) = NONE /\
      d = prepared.vs_alloca_next) \/
    FLOOKUP prepared.vs_allocas (abi_builtin_decode_output_site ready min_size max_size) =
      SOME (d,abi_decode_bytes_copy_size n)) /\
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
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_valid_bytes_resources_from_source) >> strip_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM] compile_abi_decode_memory_valid_bytes) >>
    simp[]
QED

(* Source success establishes the actual builtin's minimum/maximum length guards. *)
Theory abiValidBytesBounds
Ancestors
  abiValidBytesUnwrap abiBuiltinValidBytes abiBuiltinDecodeSetup abiDecoderBytes
  abiDecoderBytesTyped abiDecoderContract abiDecoderReentry vyperABIValid vyperABI vyperContext
  contractABI compileEnv valueEncoding venomState finite_map words list arithmetic

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

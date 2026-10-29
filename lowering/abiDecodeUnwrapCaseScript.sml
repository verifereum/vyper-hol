(* The shared wrapping decision preserves source decoding and result memory.
   The fragment premise retains the decoder's concrete execution obligation. *)
Theory abiDecodeUnwrapCase
Ancestors
  abiWrappedDecodeProps abiDecoderSingletonFragment abiDecoderTypedContract
  fragExec vyperContext valueEncoding combin exprLowering compileEnv builtinAbi

Theorem compile_abi_decode_wrapping:
  let wrapped_ty = if unwrap /\ needs_external_call_wrap ret_ty then
                     TupleT [ret_ty] else ret_ty in
    compile_type_builtin_dispatch_body cfn ce vv_ty ty (AbiDecode unwrap) ret_ty args st =
    (let (data_vv,st1) = cfn ce (expr_type (HD args)) (HD args) st in
     let (data_op,st2) = unwrap_value ce data_vv st1 in
     as_ptr_val vv_ty LocMemory
       (lower_abi_decode data_op (type_to_abi_dec_info ce.ce_struct_fields ce wrapped_ty)
         (abi_static_size ce.ce_struct_fields wrapped_ty)
         (abi_size_bound ce.ce_struct_fields wrapped_ty)
         (type_memory_bytes ce wrapped_ty) st2))
Proof
  simp[compile_type_builtin_dispatch_body_def, LET_THM]
QED

Theorem abi_decode_output_size:
  type_memory_bytes ce (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) =
    type_memory_bytes ce ty
Proof
  Cases_on `unwrap /\ needs_external_call_wrap ty` >> simp[type_memory_bytes_def]
QED

Theorem abi_decode_source_wrapping_success:
  evaluate_abi_decode (get_tenv cx)
    (if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty) bs =
  INL (if unwrap /\ needs_external_call_wrap ty then ArrayV (TupleV [v]) else v) ==>
  evaluate_type_builtin cx (AbiDecode unwrap) ty [BytesV bs] = INL v
Proof
  Cases_on `unwrap /\ needs_external_call_wrap ty` >>
  simp_tac bool_ss [] >> strip_tac >> gvs[evaluate_type_builtin_def]
QED

Theorem abi_decoder_post_unwrap:
  abi_decoder_post (if wrapped then TupleTV [tv] else tv)
    (if wrapped then ArrayV (TupleV [v]) else v) st' d outsz b cap initial =
  abi_decoder_post tv v st' d outsz b cap initial
Proof
  Cases_on `wrapped` >> simp[abi_decoder_singleton_post_function]
QED

Theorem abi_decoder_unwrap_case:
  let wrapped = (unwrap /\ needs_external_call_wrap ty) in
    evaluate_abi_decode (get_tenv cx) (if wrapped then TupleT [ty] else ty) bs =
      INL (if wrapped then ArrayV (TupleV [v]) else v) /\
    frag_exec ctx st st' P
      (abi_decoder_post (if wrapped then TupleTV [tv] else tv)
        (if wrapped then ArrayV (TupleV [v]) else v) st' d outsz b cap initial) R ==>
    frag_exec ctx st st' P
      (\t. evaluate_type_builtin cx (AbiDecode unwrap) ty [BytesV bs] = INL v /\
           abi_decoder_post tv v st' d outsz b cap initial t) R
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  `evaluate_type_builtin cx (AbiDecode unwrap) ty [BytesV bs] = INL v` by
    (irule abi_decode_source_wrapping_success >> simp[]) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [abi_decoder_post_unwrap]) >>
  irule frag_exec_conseq >>
  qexistsl_tac [`P`, `abi_decoder_post tv v st' d outsz b cap initial`, `R`] >> simp[]
QED

Theorem abi_decoder_unwrap_true_case =
  SIMP_RULE bool_ss [LET_THM] (Q.INST [`unwrap` |-> `T`] abi_decoder_unwrap_case);

Theorem abi_decoder_unwrap_false_case =
  SIMP_RULE bool_ss [LET_THM] (Q.INST [`unwrap` |-> `F`] abi_decoder_unwrap_case);

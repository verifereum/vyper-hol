(* Canonical-success correctness of both actual ABI builtin wrapping choices.
   The whole lower_abi_decode action executes; no fragment success is assumed. *)
Theory abiBuiltinUnwrapCorrect
Ancestors
  abiBuiltinDecodeCorrect abiBuiltinCanonicalPre abiBuiltinDecodeEffect
  abiDecodeUnwrapCase abiBoundaryChecks abiDecoderContract abiDecoderLoop
  abiEncoder builtinAbi fragExec compileEnv valueEncoding vyperABI vyperContext
  venomState venomExecSemantics words list

Theorem lower_abi_decode_unwrap_canonical:
  let wrapped = (unwrap /\ needs_external_call_wrap ty) in
  let wrapped_ty = if wrapped then TupleT [ty] else ty in
  let wrapped_tv = if wrapped then TupleTV [tv] else tv in
  let wrapped_v = if wrapped then ArrayV (TupleV [v]) else v in
  lower_abi_decode data (type_to_abi_dec_info sf ce wrapped_ty) min_size max_size
    (type_memory_bytes ce wrapped_ty) start = (out,final) /\ fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_canonical_pre ce (get_tenv cx) sf wrapped_ty wrapped_tv av wrapped_v start
    first last data min_size max_size src_base d b cap initial /\
  evaluate_abi_decode (get_tenv cx) wrapped_ty bs = INL wrapped_v /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = start.cs_current_bb /\ initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. evaluate_type_builtin cx (AbiDecode unwrap) ty arg_tys [BytesV bs] = INL v /\
    eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce ty)
      b cap initial actual /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `evaluate_type_builtin cx (AbiDecode unwrap) ty arg_tys [BytesV bs] = INL v` by
    (irule abi_decode_source_wrapping_success >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`ty` |-> `if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty`,
    `tv` |-> `if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv`,
    `v` |-> `if unwrap /\ needs_external_call_wrap ty then ArrayV (TupleV [v]) else v`,
    `env` |-> `get_tenv cx`] lower_abi_decode_canonical) >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp_tac bool_ss [abi_decode_output_size] >>
  Cases_on `unwrap /\ needs_external_call_wrap ty` >>
  gvs[val_in_memory_singleton_tuple, Excl "enc_def"]
QED

Theorem lower_abi_decode_unwrap_true_canonical =
  SIMP_RULE bool_ss [LET_THM] (Q.INST [`unwrap` |-> `T`] lower_abi_decode_unwrap_canonical);

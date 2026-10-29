(* Execute either wrapping choice and recover the builtin's unwrapped value.
   TOP-LEVEL: abi_decoder_unwrap_execute, abi_decoder_unwrap_true_execute.
   This consumes pure decoder inputs, with no assumed execution fragment. *)
Theory abiDecoderUnwrapExecute
Ancestors
  abiDecoderCoherentCorrect abiDecodeUnwrapCase abiWrappedDecodeProps abiDecoderCorrect
  abiBoundaryChecks
  abiDecoderEffect abiDecoderAllocation abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecoderReentry fragExec exprLowering compileEnv valueEncoding
  vyperABI vyperContext builtinAbi venomState venomExecSemantics words list

Theorem abi_decoder_unwrap_execute:
  let wrapped = (unwrap /\ needs_external_call_wrap ty) in
  let wrapped_ty = if wrapped then TupleT [ty] else ty in
  let wrapped_tv = if wrapped then TupleTV [tv] else tv in
  let wrapped_v = if wrapped then ArrayV (TupleV [v]) else v in
  compile_abi_decode_to_buf dst src opc hi (type_to_abi_dec_info sf ce wrapped_ty)
    start = ((),end_st) /\ fn_has_code start end_st func /\
  (start.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_recursive_pre ce (get_tenv cx) sf wrapped_ty wrapped_tv
    (type_to_abi_dec_info sf ce wrapped_ty) av wrapped_v
    start last src dst opc hi sb d b cap (abi_decoder_prune_vars start.cs_next_var initial) /\
  evaluate_abi_decode (get_tenv cx) wrapped_ty bs = INL wrapped_v /\
  abi_decoder_budget first last b cap initial /\ first <= start.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?t. evaluate_type_builtin cx (AbiDecode unwrap) ty [BytesV bs] = INL v /\
    val_in_memory tv v d t.vs_memory /\
    abi_decoder_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
      limit_st d (type_memory_bytes ce ty) b cap initial t /\
    t.vs_current_bb = end_st.cs_current_bb /\ t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~t.vs_halted /\ abi_decode_sim ctx func initial t
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `evaluate_type_builtin cx (AbiDecode unwrap) ty [BytesV bs] = INL v` by
    (irule abi_decode_source_wrapping_success >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`ty` |-> `if unwrap /\ needs_external_call_wrap ty then TupleT [ty] else ty`,
    `tv` |-> `if unwrap /\ needs_external_call_wrap ty then TupleTV [tv] else tv`,
    `v` |-> `if unwrap /\ needs_external_call_wrap ty then ArrayV (TupleV [v]) else v`,
    `env` |-> `get_tenv cx`] abi_decoder_decode) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  simp_tac bool_ss [abi_decode_output_size] >>
  Cases_on `unwrap /\ needs_external_call_wrap ty` >>
  gvs[val_in_memory_singleton_tuple, Excl "enc_def"]
QED

Theorem abi_decoder_unwrap_true_execute =
  SIMP_RULE bool_ss [LET_THM] (Q.INST [`unwrap` |-> `T`] abi_decoder_unwrap_execute);

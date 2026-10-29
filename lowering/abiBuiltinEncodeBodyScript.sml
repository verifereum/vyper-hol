(* Execute every translated recursive descriptor followed by the actual builtin
   length store. Setup and producer input establishment are separate obligations. *)
Theory abiBuiltinEncodeBody
Ancestors
  abiBuiltinEncodeCompose abiBuiltinEncodeCode abiEncoderCorrectRecursive abiEncoderCorrect
  abiEncoderAppend abiEncoderCounters abiDecoderEffect abiDecoderAppend abiDecoderContract
  abiDecoderReentry abiDecoderLoop fragExec compileEnv exprLowering valueEncoding
  venomState venomExecSemantics words list arithmetic

Theorem abi_builtin_encode_body_finish:
  compile_abi_encode_to_buf dst src (type_to_abi_enc_info sf ce ty) ready = (len_op,body_end) /\
  abi_builtin_encode_finish buf len_op mid_size body_end = ((),final) /\
  fn_has_code ready final func /\
  (ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_pre (type_to_abi_enc_info sf ce ty) at av ready src dst sb source_cap
    (p+32+mid_size) b cap initial /\
  eval_operand buf initial = SOME (n2w p) /\ abi_decoder_operand_live ready.cs_next_var buf /\
  (p+32+mid_size+LENGTH (enc at av) <= b \/ b+cap <= p) /\
  abi_decoder_budget first last b cap initial /\ first <= ready.cs_next_id /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = ready.cs_current_bb /\
  initial.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH (enc at av)+mid_size) /\
    mem_bytes_at (p+32+mid_size) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_bytes_at (p+32) mid_size actual.vs_memory = mem_bytes_at (p+32) mid_size initial.vs_memory /\
    abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
      limit_st p (32+mid_size+LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends body_end final` by
    (irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`ready`, `body_end`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_correct (type_to_abi_enc_info sf ce ty)` by simp[abi_encoder_correct_translation] >>
  `body_end.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_id <= last /\
   body_end.cs_next_id <= final.cs_next_id` by (Cases_on `mid_size > 0` >> gvs[] >> decide_tac) >>
  qpat_assum `final.cs_blocks = body_end.cs_blocks` (fn blocks =>
    qpat_assum `final.cs_current_bb = body_end.cs_current_bb` (fn label =>
    qpat_assum `ready.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [blocks,label]))) >>
  mp_tac (Q.INST [`start` |-> `ready`, `end_st` |-> `body_end`, `out` |-> `len_op`,
    `d` |-> `p+32+mid_size:num`, `ctx` |-> `ctx`,
    `ei` |-> `type_to_abi_enc_info sf ce ty`] abi_encoder_correct_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial encoded` >>
  `p < dimword (:256)` by
    (qpat_assum `abi_encoder_pre _ _ _ _ _ _ _ _ _ _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_pre_def]) >> decide_tac) >>
  mp_tac (Q.INST [`encoded_len` |-> `len_op`, `len` |-> `LENGTH (enc at av)`,
    `bytes` |-> `enc at av`] abi_builtin_encode_compose) >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED

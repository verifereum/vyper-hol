(* Source-value correctness of the actual bytes and string encoder branches. *)
Theory abiEncoderSourceCorrect
Ancestors
  abiEncoderSourceInput abiEncoderBytes abiEncoderInput exprLowering abiDecoderReentry
  abiDecoderContract valueEncoding vyperABI vyperTyping compileEnv emitHelper venomState
  venomExecSemantics words list

Theorem abi_encoder_source_bytes_sequence:
  compile_abi_encode_to_buf dst src
    (type_to_abi_enc_info sf ce (BaseT (BytesT (Dynamic n)))) st = (out,final) /\
  value_has_type (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) /\
  val_wf (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bs) sb s.vs_memory /\
  n < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\ db+LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) < dimword (:256) /\
  (sb+type_memory_size (BaseTV (BytesT (Dynamic n))) <= db \/
    db+LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)) <= sb) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    mem_bytes_at db (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) actual.vs_memory =
      enc (Bytes NONE) (contractABI$BytesV bs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs)))) /\
    fresh_vars_wrt limit_st actual /\
    abi_decode_frame db (LENGTH (enc (Bytes NONE) (contractABI$BytesV bs))) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  strip_tac >> drule_all (SIMP_RULE (srw_ss()) [type_to_abi_enc_info_def,
    vyper_to_abi_type_def, vyper_base_to_abi_type_def, vyper_to_abi_def] abi_encoder_bytes_source_input) >>
  strip_tac >> mp_tac (Q.INST [`dst` |-> `dst`, `src` |-> `src`, `maxlen` |-> `n`,
    `at` |-> `Bytes NONE`, `av` |-> `contractABI$BytesV bs`,
    `cap` |-> `type_memory_size (BaseTV (BytesT (Dynamic n)))`] abi_encoder_bytes_sequence) >>
  fs[type_to_abi_enc_info_def, Excl "enc_def"]
QED

Theorem abi_encoder_source_string_sequence:
  compile_abi_encode_to_buf dst src
    (type_to_abi_enc_info sf ce (BaseT (StringT n))) st = (out,final) /\
  value_has_type (BaseTV (StringT n)) (StringV text) /\
  val_wf (BaseTV (StringT n)) (StringV text) /\
  val_in_memory (BaseTV (StringT n)) (StringV text) sb s.vs_memory /\
  n < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb < dimword (:256) /\
  db+LENGTH (enc String (contractABI$BytesV (MAP (n2w o ORD) text))) < dimword (:256) /\
  (sb+type_memory_size (BaseTV (StringT n)) <= db \/
    db+LENGTH (enc String (contractABI$BytesV (MAP (n2w o ORD) text))) <= sb) /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    mem_bytes_at db (LENGTH (enc String (contractABI$BytesV (MAP (n2w o ORD) text)))) actual.vs_memory =
      enc String (contractABI$BytesV (MAP (n2w o ORD) text)) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc String (contractABI$BytesV (MAP (n2w o ORD) text))))) /\
    fresh_vars_wrt limit_st actual /\
    abi_decode_frame db (LENGTH (enc String (contractABI$BytesV (MAP (n2w o ORD) text)))) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  strip_tac >> drule_all (SIMP_RULE (srw_ss()) [type_to_abi_enc_info_def,
    vyper_to_abi_type_def, vyper_base_to_abi_type_def, vyper_to_abi_def] abi_encoder_string_source_input) >>
  strip_tac >> mp_tac (Q.INST [`dst` |-> `dst`, `src` |-> `src`, `maxlen` |-> `n`,
    `at` |-> `String`, `av` |-> `contractABI$BytesV (MAP (n2w o ORD) text)`,
    `cap` |-> `type_memory_size (BaseTV (StringT n))`] abi_encoder_bytes_sequence) >>
  fs[type_to_abi_enc_info_def, Excl "enc_def"]
QED

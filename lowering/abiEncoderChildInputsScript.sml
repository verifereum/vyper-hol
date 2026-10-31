(* Incoming source data and the enclosing output buffer for child encoders. *)
Theory abiEncoderChildInputs
Ancestors
  abiEncoderCorrect abiEncoderInput abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract compileEnv valueEncoding venomState words arithmetic

Definition abi_encoder_buffer_pre_def:
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap s <=>
    abi_encoder_input ei at av sb source_cap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
    abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
    sb+source_cap < dimword (:256) /\ d+output_size < dimword (:256) /\
    (sb+source_cap <= d \/ d+output_size <= sb) /\
    (sb+source_cap <= b \/ b+cap <= sb) /\ (d+output_size <= b \/ b+cap <= d)
End

Theorem abi_encoder_buffer_pre_exact:
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d (LENGTH (enc at av)) b cap s <=>
  abi_encoder_pre ei at av st src dst sb source_cap d b cap s
Proof
  simp[abi_encoder_buffer_pre_def, abi_encoder_pre_def]
QED

Theorem abi_encoder_child_pre_address:
  abi_encoder_buffer_pre ei at av st src dst sb source_cap d output_size b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\ st.cs_next_var <= child_st.cs_next_var /\
  abi_decoder_operand_live child_st.cs_next_var child_dst /\
  eval_operand child_dst actual = SOME (n2w (d+offset)) /\
  offset+LENGTH (enc at av) <= output_size ==>
  abi_encoder_pre ei at av child_st src child_dst sb source_cap (d+offset) b cap actual
Proof
  simp_tac bool_ss [abi_encoder_buffer_pre_def, abi_decoder_address_frame_def, abi_encoder_pre_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src actual = SOME (n2w sb)` by (first_x_assum irule >> simp[]) >>
  `abi_decoder_operand_live child_st.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

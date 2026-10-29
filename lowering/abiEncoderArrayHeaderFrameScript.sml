(* Repeated encoder headers overwrite only their three generated registers. *)
Theory abiEncoderArrayHeaderFrame
Ancestors
  abiEncoderArrayHeader abiDecoderLoopRegisters abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderEffect abiDecoderAllocation abiDecoderContract
  compileEnv venomState venomExecSemantics words arithmetic

Theorem abi_encode_array_header_registers:
  next+3 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st (abi_encode_array_header_state
    (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) i n s)
Proof
  strip_tac >> `next < limit_st.cs_next_var /\ next+1 < limit_st.cs_next_var /\
    next+2 < limit_st.cs_next_var` by decide_tac >>
  asm_simp_tac bool_ss [abi_encode_array_header_state_def, abi_decoder_generated_update_fresh]
QED

Theorem abi_encode_array_header_address_frame:
  abi_decoder_address_frame next s (jump_to lbl (abi_encode_array_header_state
    (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
    (STRING #"%" (toString (next+2))) i n s))
Proof
  simp_tac bool_ss [abi_decoder_address_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `next <= next+1 /\ next <= next+2` by simp[] >>
      imp_res_tac abi_decoder_operand_live_mono >>
      asm_simp_tac bool_ss [abi_decoder_operand_jump, abi_encode_array_header_state_def,
        abi_decoder_generated_update_operand]) >>
  simp[abi_encode_array_header_state_def, jump_to_def, update_var_def]
QED

Theorem abi_encode_array_header_effect:
  next+3 <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  abi_decoder_budget first last b cap s ==>
  abi_decoder_effect first last lo hi next limit_st d sz b cap s
    (jump_to lbl (abi_encode_array_header_state
      (STRING #"%" (toString next)) (STRING #"%" (toString (next+1)))
      (STRING #"%" (toString (next+2))) i n s))
Proof
  strip_tac >> drule_all abi_encode_array_header_registers >> disch_tac >>
  irule abi_decoder_address_effect >> asm_simp_tac bool_ss [abi_decoder_fresh_jump] >>
  qexists_tac `next` >> simp[abi_encode_array_header_address_frame]
QED

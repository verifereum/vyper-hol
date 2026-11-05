(* Persistent array observations across repeated loop header execution. *)
Theory ctorAbiActualArrayHeader
Ancestors
  ctorAbiActualArrayBody ctorAbiActualArrayInvariant ctorAbiActualWorld ctorAbiActualNarrow
  abiDecoderLoopRegisters abiDecoderExecution abiDecoderLoop abiDecoderArrayBackedge
  abiDecoderDynamicLoopSetup abiDecoderContract abiDecoderReentry
  venomState venomExecSemantics compileEnv words list arithmetic finite_map

Theorem ctor_actual_array_header_observation:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  next <= first /\ first+4 <= limit_st.cs_next_var ==>
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s))
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st s` by fs[ctor_actual_array_observation_def] >>
  drule_all abi_decoder_header_registers >> strip_tac >>
  qabbrev_tac `t = jump_to lbl (abi_decode_header_state (STRING #"%" (toString first))
    (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
    (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  `abi_decoder_address_frame first s t /\ t.vs_labels = s.vs_labels /\
   fresh_vars_wrt limit_st t` by
    (simp[Abbr `t`, abi_decoder_address_frame_def, abi_decoder_operand_jump,
      abi_decoder_fresh_jump] >>
     conj_tac >- simp[abi_decode_header_state_def, jump_to_def, update_var_def] >>
     simp[abi_decode_header_state_def, jump_to_def, update_var_def]) >>
  `abi_encoder_registered_effect {} [] s t` by
    (irule ctor_actual_empty_effect >>
     simp[Abbr `t`, abi_decode_header_state_def, jump_to_def, update_var_def]) >>
  irule ctor_actual_array_observation_address >>
  asm_simp_tac bool_ss [] >> qexistsl [`first`, `s`] >>
  asm_simp_tac bool_ss []
QED

Theorem ctor_actual_array_header_run:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  abi_decode_loop_cfg func hdr body_lbl exit_lbl hid ip src DLOAD
    (STRING #"%" (toString first)) (STRING #"%" (toString (first+1)))
    (STRING #"%" (toString (first+2))) (STRING #"%" (toString (first+3))) /\
  next <= first /\ first+4 <= limit_st.cs_next_var /\
  abi_decoder_operand_live next src /\
  s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME srcaddr /\
  abi_decode_load DLOAD srcaddr s = n2w (LENGTH vs) /\
  slot < dimword (:256) /\ LENGTH vs < dimword (:256) ==>
  ?h. ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then body_lbl else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h
Proof
  strip_tac >>
  `j <= LENGTH vs /\ mload slot s = n2w j` by fs[ctor_actual_array_observation_def] >>
  `abi_decode_loop_ready hdr ip src DLOAD (n2w slot) srcaddr (LENGTH vs) j s` by
    simp[abi_decode_loop_ready_def, w2n_n2w] >>
  `src <> Var (STRING #"%" (toString first))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  `STRING #"%" (toString first) <> STRING #"%" (toString (first+1))` by simp[] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_ready_header_sim >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all ctor_actual_array_header_observation >> strip_tac >>
  qexists `jump_to (if j < LENGTH vs then body_lbl else exit_lbl)
    (abi_decode_header_state (STRING #"%" (toString first))
      (STRING #"%" (toString (first+1))) (STRING #"%" (toString (first+2)))
      (STRING #"%" (toString (first+3))) j (LENGTH vs) s)` >>
  asm_simp_tac bool_ss [] >>
  simp[jump_to_def, abi_decode_header_state_def, update_var_def]
QED

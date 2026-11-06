(* Precise identity and actual loop-header effects. *)
Theory abiScratchDecoderLoopControl
Ancestors
  abiScratchEncoderContract abiScratchLeafEffect abiScratchAddress abiScratchEffect
  abiDecoderDynamicLoopSetup abiDecoderLoopRegisters abiDecoderExecution abiDecoderContract
  abiDecoderFrame abiDecoderAllocation abiDecoderReentry compileEnv venomState words list
  arithmetic

Theorem abi_scratch_effect_refl:
  fresh_vars_wrt limit_st s /\ abi_sites_decoder_budget sites first last b cap s ==>
  abi_sites_scratch_effect sites first last lo hi next limit_st d sz b cap s s
Proof
  strip_tac >> irule abi_scratch_leaf_effect >> simp[abi_decode_frame_def]
QED

Theorem abi_scratch_decoder_header_effect:
  next <= first_var /\ first_var + 4 + abi_decode_position_header_delta base_op <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap s
    (jump_to lbl (abi_decode_position_header_state base_op first_var B sb i ncount s))
Proof
  strip_tac >> drule_all abi_decoder_position_header_registers >> strip_tac >>
  qabbrev_tac `h = jump_to lbl (abi_decode_position_header_state base_op first_var B sb i ncount s)` >>
  `fresh_vars_wrt limit_st h` by simp[Abbr`h`] >>
  `abi_decoder_address_frame first_var s h` by
    (asm_simp_tac bool_ss [abi_decoder_address_frame_def, Abbr`h`, abi_decoder_operand_jump] >>
     Cases_on `base_op = Lit 0w` >>
     simp[jump_to_def, abi_decode_position_header_state_def, update_var_def]) >>
  irule abi_scratch_effect_widen >>
  qexistsl_tac [`d`, `hi`, `lo`, `first_var`, `sz`] >>
  asm_simp_tac bool_ss [LESS_EQ_REFL] >>
  irule abi_scratch_address_effect >> asm_simp_tac bool_ss []
QED

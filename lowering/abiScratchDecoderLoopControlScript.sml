(* Precise identity and actual loop-header effects. *)
Theory abiScratchDecoderLoopControl
Ancestors
  abiScratchEncoderContract abiScratchLeafEffect abiScratchAddressEffect abiScratchEffectWiden
  abiDecoderDynamicLoopSetup abiDecoderLoopRegisters abiDecoderExecution abiDecoderContract abiDecoderFrame
  abiDecoderAllocation abiDecoderReentry compileEnv venomState words list arithmetic

Theorem abi_scratch_effect_refl:
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap s s
Proof
  strip_tac >> irule abi_scratch_leaf_effect >> simp[abi_decode_frame_def]
QED

Theorem abi_scratch_decoder_header_effect:
  next <= first_var /\ first_var + 4 <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s ==>
  abi_scratch_effect first last lo hi next limit_st d sz b cap s
    (jump_to lbl (abi_decode_header_state (STRING #"%" (toString first_var))
      (STRING #"%" (toString (first_var+1))) (STRING #"%" (toString (first_var+2)))
      (STRING #"%" (toString (first_var+3))) i ncount s))
Proof
  strip_tac >> drule_all abi_decoder_header_registers >> strip_tac >>
  qabbrev_tac `h = jump_to lbl (abi_decode_header_state (STRING #"%" (toString first_var))
    (STRING #"%" (toString (first_var+1))) (STRING #"%" (toString (first_var+2)))
    (STRING #"%" (toString (first_var+3))) i ncount s)` >>
  `fresh_vars_wrt limit_st h` by simp[Abbr`h`] >>
  `abi_decoder_address_frame first_var s h` by
    (asm_simp_tac bool_ss [abi_decoder_address_frame_def, Abbr`h`, abi_decoder_operand_jump] >>
     simp[jump_to_def, abi_decode_header_state_def, update_var_def]) >>
  irule abi_scratch_effect_widen >>
  qexistsl_tac [`d`, `hi`, `lo`, `first_var`, `sz`] >>
  asm_simp_tac bool_ss [LESS_EQ_REFL] >>
  irule abi_scratch_address_effect >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_LOOP_CONTROL_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical decoder loop control not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderLoopControl");


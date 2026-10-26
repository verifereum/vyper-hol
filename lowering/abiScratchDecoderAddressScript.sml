(* Address-only code preserves physical ranges, actual source bytes and older operands. *)
Theory abiScratchDecoderAddress
Ancestors
  abiScratchDecoderContract abiScratchDecoderTransport abiScratchEncoderContract
  abiScratchAddressEffect abiDecoderArrayBody abiDecoderArraySetupInputs abiDecoderDynamicLoopSetup
  abiDecoderReentry abiDecoderContract abiDecodeRanges compileEnv
  valueEncoding venomState words arithmetic

Theorem abi_scratch_decoder_address_observations:
  abi_scratch_decoder_ranges opc hi_op src dst sb len d sz first last b cap initial /\
  abi_decoder_address_frame next initial prepared /\ fresh_vars_wrt limit_st prepared /\
  abi_decoder_budget first last b cap initial /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi_op /\ next <= new_next ==>
  abi_scratch_decoder_ranges opc hi_op src dst sb len d sz first last b cap prepared /\
  abi_decode_source opc prepared = abi_decode_source opc initial /\
  abi_decoder_budget first last b cap prepared /\
  abi_decoder_operand_live new_next src /\ abi_decoder_operand_live new_next dst /\
  abi_decoder_operand_live new_next hi_op
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_scratch_effect first last first last next limit_st d sz b cap initial prepared` by
    (irule abi_scratch_address_effect >> asm_simp_tac bool_ss []) >>
  drule_all abi_scratch_decoder_ranges_effect >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  `abi_decoder_operand_live new_next src /\ abi_decoder_operand_live new_next dst /\
   abi_decoder_operand_live new_next hi_op` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `next` >> asm_simp_tac bool_ss []) >>
  fs[abi_scratch_effect_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_ADDRESS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical address observations not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderAddress");


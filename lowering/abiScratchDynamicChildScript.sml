(* Transport physical scratch input across a source-address prefix. *)
Theory abiScratchDynamicChild
Ancestors
  abiScratchMemberAdapter
  abiScratchChild abiScratchArrayDynamicRound abiScratchEncoderContract abiScratchAddress
  abiScratchAfterAddress abiScratchFootprint abiEncoderAddressReach abiDecoderDynamicLoopSetup
  abiDecoderAllocation abiDecoderFootprint abiDecoderFrame abiDecoderReentry abiDecoderContract
  abiDecoderLoop compileEnv valueEncoding contractABI venomState finite_map words list
  arithmetic

Theorem abi_scratch_input_address:
  abi_scratch_input ei at av st src dst sb source_cap d sz first last b cap initial /\
  abi_decoder_address_frame st.cs_next_var initial actual /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_scratch_input ei at av prepared src dst sb source_cap d sz first last b cap actual
Proof
  simp_tac bool_ss [abi_scratch_input_def, abi_decoder_address_frame_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d)` by
    (conj_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial` by
    simp[abi_decoder_child_scratch_def] >>
  asm_simp_tac bool_ss [] >>
  conj_tac >> irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]
QED

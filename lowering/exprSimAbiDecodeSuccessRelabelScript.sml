Theory exprSimAbiDecodeSuccessRelabel
Ancestors
  exprSimAbiDecodeImmutableOutcome exprSimAbiDecodeBoundary exprSimAbiDecodeQuantifiedLift
  abiDecoderSiteEffect exprSimAbiGasBridge abiBuiltinDecodeSetup venomState

Theorem abi_decode_eval_operand_entry_current_bb[local]:
  eval_operand op (s with vs_current_bb := L) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem abi_decode_site_effect_entry_current_bb:
  decode_site_effect ctx fn next writes (s with vs_current_bb := L) t =
  decode_site_effect ctx fn next writes s t
Proof
  simp[decode_site_effect_def, decode_static_frame_def, decode_memory_frame_def, decode_upper_frame_def,
       abi_decode_eval_operand_entry_current_bb]
QED

Theorem abi_decode_immutable_success_relabel:
  abi_decode_immutable_success ce env ty tv bs out d
    (start_relabel L ids start) (start_swap start L ids final)
    ctx func cx es (s with vs_current_bb := L) t ==>
  abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t
Proof
  simp[abi_decode_immutable_success_def, abi_decode_success_closed_def,
       abi_decode_success_post_def, abi_decode_immutable_memory_def,
       abi_decode_window_frame_def, start_relabel_def, start_swap_def, abi_builtin_decode_output_site_def,
       abi_decode_site_effect_entry_current_bb] >>
  Cases_on `NULL (emitted_blocks start final)` >> simp[] >> metis_tac[]
QED

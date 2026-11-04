(* Compose pure header/pointer effects around the output allocation. *)
Theory abiBuiltinSetupFrames
Ancestors
  abiBuiltinAllocation abiBuiltinDecodeSetup abiBuiltinDecodeHeader abiBuiltinPrefix
  abiDecoderReentry abiDecoderDynamicLoopSetup compileEnv emitHelperProps exprLoweringProps
  venomState words arithmetic list

Theorem abi_builtin_allocation_frame_prefix:
  abi_decoder_address_frame next s prepared /\
  abi_builtin_allocation_frame child_next site outsz prepared t /\ next <= child_next ==>
  abi_builtin_allocation_frame next site outsz s t
Proof
  simp_tac bool_ss [abi_decoder_address_frame_def, abi_builtin_allocation_frame_def] >>
  strip_tac >>
  mp_tac (Q.INST [`s` |-> `s:venom_state`, `t` |-> `prepared:venom_state`]
    abi_builtin_allocate_state_transport) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_operand_live child_next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >> metis_tac[]
QED

Theorem abi_builtin_allocation_frame_suffix:
  abi_builtin_allocation_frame next site outsz s allocated /\
  abi_decoder_address_frame child_next allocated t /\ next <= child_next ==>
  abi_builtin_allocation_frame next site outsz s t
Proof
  simp_tac bool_ss [abi_builtin_allocation_frame_def, abi_decoder_address_frame_def] >>
  strip_tac >> asm_simp_tac bool_ss [] >> rpt strip_tac >>
  `abi_decoder_operand_live child_next op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `next` >> simp[]) >> metis_tac[]
QED

Theorem abi_builtin_decode_header_live:
  abi_builtin_decode_header data min_size max_size st = (inputs,header_st) ==>
  abi_decoder_operand_live header_st.cs_next_var (FST inputs) /\
  abi_decoder_operand_live header_st.cs_next_var (SND inputs)
Proof
  strip_tac >> drule abi_builtin_decode_header_outputs >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  rpt strip_tac >> decide_tac
QED

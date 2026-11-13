(* Nonbulk decoder loops necessarily emit new basic blocks. *)
Theory decoderBlockGrowth
Ancestors
  abiDecoderArrayLoopInit abiDecoderArrayInit abiDecoderLoopEmit
  abiDecoderRecursiveLoopLayout abiDecoderArraySetupCode abiDecoderAppend
  abiDecoderContract compileEnv list

Theorem nonbulk_decoder_blocks_grow:
  compile_abi_decode_to_buf dst src opc base_op hi (DecDynArray di hs ms dyn n)
    st = ((),last) /\
  (dyn \/ dec_info_needs_clamp di) /\ abi_decode_source_opcode opc ==>
  st.cs_blocks <> last.cs_blocks
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_decode_loop_array_trace >> strip_tac >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >>
  disch_then (strip_assume_tac o MATCH_MP abi_decoder_loop_suffix_facts) >>
  fs[cs_extends_def]
QED

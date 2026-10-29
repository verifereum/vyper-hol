(* Actual word decoders preserve the precise physical scratch footprint.
   The old scalar sequence proof is reused with a derived empty reservation. *)
Theory abiScratchDecoderWord
Ancestors
  abiScratchDecoderPrefix abiScratchDecoderContract abiScratchLeafEffect abiScratchEncoderContract
  abiDecoderReentryPrimitive abiDecoderPrimitive abiDecoderCorrectWord abiDecoderTypedContract
  abiDecoderCoherence abiDecoderContract abiDecoderReentry abiDecoderLoop abiDecoderFrame
  abiDecoderAllocation abiEncoder fragExec compileEnv valueEncoding vyperABI contractABI
  venomState words list

Theorem abi_scratch_decoder_word:
  type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce ty = DecPrimWord clamp ==>
  abi_scratch_decoder ce env sf ty tv
Proof
  strip_tac >> simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_scratch_decoder_word_pre >> strip_tac >>
  drule abi_decoder_primitive_source >> strip_tac >>
  drule_all abi_decoder_primitive_reentry_from_state >>
    disch_then (qspec_then `ctx` assume_tac) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `start.cs_next_var`, `sz` |-> `32:num`] abi_scratch_leaf_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

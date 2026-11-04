(* Actual-source singleton child input, without a canonical encoding premise. *)
Theory entrySingletonValidInput
Ancestors
  abiValidSingletonPrefix abiValidSingletonArray abiDecoderValidContract
  abiDecoderArraySetupInputs abiDecoderDynamicLoopSetup abiDecoderContract
  abiDecoderTypedContract abiDecoderCoherence abiDecoderReentry
  compileEnv valueEncoding vyperABI contractABI venomState words list arithmetic

Theorem decoder_valid_singleton_child_input:
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
  is_dynamic (vyper_to_abi_type env ty) /\
  vyper_decode_valid_enc (Tuple [vyper_to_abi_type env ty]) bs /\
  dec (Tuple [vyper_to_abi_type env ty]) bs = ListV [av] /\
  abi_head_word bs <= LENGTH bs /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d (type_memory_bytes ce ty) b cap before /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc before) = bs /\
  abi_decoder_address_frame st.cs_next_var before after /\
  st.cs_next_var <= ready.cs_next_var /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_operand_live ready.cs_next_var childsrc /\
  abi_decoder_operand_live ready.cs_next_var childdst /\
  eval_operand childsrc after = SOME (n2w (sb + abi_head_word bs)) /\
  eval_operand childdst after = SOME (n2w d) ==>
  abi_decoder_valid_pre ce env sf ty tv (DROP (abi_head_word bs) bs) v
    ready childsrc childdst opc hi (sb + abi_head_word bs) d b cap after
Proof
  strip_tac >>
  `sb + LENGTH bs < dimword (:256)` by fs[abi_decoder_ranges_def] >>
  drule_all abi_valid_singleton_dynamic_decode >> strip_tac >>
  drule_all abi_valid_singleton_dynamic_load >> strip_tac >>
  drule_all abi_decoder_address_frame_ranges >> strip_tac >>
  drule_all abi_decoder_address_frame_source >>
  disch_then (qspec_then `opc` assume_tac) >>
  `abi_decoder_ranges opc hi childsrc childdst (sb + abi_head_word bs)
    (LENGTH (DROP (abi_head_word bs) bs)) d (type_memory_bytes ce ty) b cap after` by
    (simp_tac bool_ss [LENGTH_DROP] >> irule abi_decoder_suffix_ranges >>
     asm_simp_tac bool_ss [] >> qexistsl_tac [`dst`, `src`] >>
     asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live ready.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
     asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss [abi_decoder_valid_pre_def]
QED

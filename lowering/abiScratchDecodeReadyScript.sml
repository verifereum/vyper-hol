(* Real builtin setup establishes physical recursive input on the original bytes. *)
Theory abiScratchDecodeReady
Ancestors
  abiScratchDecodeInput abiScratchDecoderContract abiScratchFootprint abiDecoderFootprint
  abiBuiltinAllocation abiBuiltinDecodeSetup abiBuiltinSetupExecute abiDecoderCoherence
  abiDecoderTypedContract abiDecoderReentry abiDecoderContract abiDecoderAllocation
  abiDecoderArrayInitExec abiDecodeRanges compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic

Theorem abi_scratch_decode_ranges:
  abi_scratch_decode_resources st first last min_size max_size outsz cnt p d b cap initial /\
  abi_builtin_allocation_frame next (abi_builtin_decode_output_site st min_size max_size)
    outsz initial prepared /\
  eval_operand src prepared = SOME (n2w (p + 32)) /\
  eval_operand dst prepared = SOME (n2w d) /\
  eval_operand hi prepared = SOME (n2w (p + 32 + cnt)) ==>
  abi_scratch_decoder_ranges MLOAD hi src dst (p + 32) cnt d outsz first last b cap prepared
Proof
  simp_tac bool_ss [abi_scratch_decode_resources_def, LET_THM] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state (abi_builtin_decode_output_site st min_size max_size) outsz initial)` by
    fs[abi_builtin_allocation_frame_def, abi_decoder_child_scratch_def] >>
  asm_simp_tac bool_ss [abi_scratch_decoder_ranges_def, abi_decode_source_opcode_def] >>
  disj2_tac >> qexists_tac `p + 32 + cnt` >> asm_simp_tac bool_ss [LESS_EQ_REFL]
QED

Theorem abi_scratch_decode_pre_ready:
  abi_builtin_decode_setup data min_size max_size (type_memory_bytes ce ty) st = (ops,ready) /\
  abi_scratch_decode_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap initial /\
  abi_builtin_allocation_frame st.cs_next_var (abi_builtin_decode_output_site st min_size max_size)
    (type_memory_bytes ce ty) initial prepared /\
  eval_operand (FST ops) prepared = SOME (n2w d) /\
  eval_operand (FST (SND ops)) prepared = SOME (n2w (p + 32)) /\
  eval_operand (SND (SND ops)) prepared = SOME (n2w (p + 32 + LENGTH bs)) ==>
  first <= ready.cs_next_id /\ abi_decoder_budget first last b cap prepared /\
  abi_scratch_decoder_input ce env sf ty tv bs v ready (FST (SND ops)) (FST ops)
    MLOAD (SND (SND ops)) (p + 32) d first last b cap prepared
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_decode_setup_live >> strip_tac >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  drule_all abi_scratch_decode_source >> strip_tac >>
  qpat_assum `abi_scratch_decode_pre ce env sf ty tv bs v st first last data min_size max_size p d b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decode_pre_def]) >>
  qpat_assum `abi_scratch_decode_resources _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_scratch_decode_resources_def, LET_THM]) >>
  `first <= ready.cs_next_id` by asm_simp_tac bool_ss [] >>
  `abi_decoder_budget first last b cap prepared` by
    (mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
       `site` |-> `abi_builtin_decode_output_site st min_size max_size`,
       `outsz` |-> `type_memory_bytes ce ty`, `s` |-> `initial:venom_state`,
       `t` |-> `prepared:venom_state`] abi_builtin_allocation_frame_budget) >>
     asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`next` |-> `st.cs_next_var`,
    `cnt` |-> `LENGTH (bs:word8 list)`, `outsz` |-> `type_memory_bytes ce ty`,
    `src` |-> `FST (SND (ops:operand # operand # operand))`,
    `dst` |-> `FST (ops:operand # operand # operand)`,
    `hi` |-> `SND (SND (ops:operand # operand # operand))`] abi_scratch_decode_ranges) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qpat_assum `abi_builtin_allocation_frame _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_allocation_frame_def]) >>
  asm_simp_tac (srw_ss()) [abi_scratch_decoder_input_def, abi_decode_source_def]
QED

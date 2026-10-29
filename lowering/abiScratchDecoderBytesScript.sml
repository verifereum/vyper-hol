(* Bytes/String execution writes only its output buffer and preserves actual allocations. *)
Theory abiScratchDecoderBytes
Ancestors
  abiScratchDecoderRanges abiScratchDecoderContract abiScratchLeafEffect abiScratchEncoderContract
  abiDecoderValidBytesInput abiDecoderValidBytesCorrect abiDecoderValidContract
  abiDecoderBytesTyped abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiDecoderCoherence abiDecoderLoop abiDecoderFrame abiDecoderAllocation abiEncoder
  fragExec compileEnv valueEncoding vyperABI contractABI venomState words list

Theorem abi_scratch_decoder_bytestring:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) ==>
  abi_scratch_decoder ce env sf ty tv
Proof
  disch_then assume_tac >> simp_tac bool_ss [abi_scratch_decoder_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_input_point >> strip_tac >>
  drule_all abi_decoder_valid_bytes_input >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_decoder_valid_bytes_reach >>
    disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `val_in_memory tv v d actual.vs_memory` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  qpat_assum `type_memory_bytes ce ty = abi_decode_bytes_copy_size n`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM th]) >>
      PURE_REWRITE_TAC [GSYM th]) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `t` |-> `actual:venom_state`,
    `lo` |-> `start.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `next` |-> `start.cs_next_var`, `sz` |-> `type_memory_bytes ce ty`] abi_scratch_leaf_effect) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

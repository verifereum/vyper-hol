(* Counted scalar decoder execution with physical scratch effects. *)
Theory bodyIntCallDecoderCountedLeaves
Ancestors
  bodyIntCallDecoderCountedContract bodyIntCallDecoderCountedPrimitive
  abiScratchDecoderTuple abiScratchLeafEffect abiDecoderReentryPointer
  abiDecoderClampedWord abiDecoderPrimitiveCaller abiDecoderContract
  abiDecoderCoherence abiDecoderTypedContract abiScratchDecoderContract
  abiDecoderValidBytesInput abiValidBytesReentry abiDecoderValidBytes abiDecoderBytesTyped
  abiScratchDecoderRanges
  abiDecoderFrame abiDecoderAllocation abiScratchEncoderContract
  abiEncoder exprLowering compileEnv fragExec fragGasPath
  entrySinkExtraction instIdxIndep venomState venomExecSemantics
  vyperAST valueEncoding list

Theorem intcall_scratch_decoder_counted_word:
  type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce ty = DecPrimWord clamp ==>
  intcall_scratch_decoder_counted ce env sf ty tv
Proof
  strip_tac >> simp_tac bool_ss [intcall_scratch_decoder_counted_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all abi_scratch_decoder_word_pre >> strip_tac >>
  drule abi_decoder_primitive_source >> strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_recursive_pre_def, abi_decoder_pre_def, abi_decoder_ranges_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts start end_st)` by fs[EVERY_CONJ] >>
  drule_all abi_decoder_primitive_reentry_sequence >> strip_tac >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path ctx func initial n (OK endpoint)` >>
  `abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
    limit_st d 32 b cap initial endpoint` by
    (irule abi_scratch_leaf_effect >>
     fs[Abbr `endpoint`, fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`endpoint`, `n`] >>
  fs[Abbr `endpoint`] >> first_assum ACCEPT_TAC
QED

Theorem intcall_scratch_decoder_counted_flag:
  intcall_scratch_decoder_counted ce env sf (FlagT nsid) tv
Proof
  irule intcall_scratch_decoder_counted_word >> simp[type_to_abi_dec_info_def]
QED

Theorem intcall_scratch_decoder_counted_bytestring:
  (ty = BaseT (BytesT (Dynamic n)) \/ ty = BaseT (StringT n)) ==>
  intcall_scratch_decoder_counted ce env sf ty tv
Proof
  disch_then assume_tac >> simp_tac bool_ss [intcall_scratch_decoder_counted_def] >> rpt gen_tac >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_decoder_input_point >> strip_tac >>
  drule_all abi_decoder_valid_bytes_input >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_decode_source_opcode opc` by
    fs[abi_decoder_valid_bytes_pre_def, Excl "dec_def", Excl "valid_enc_def"] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule_all abi_decoder_valid_bytes_reentry >> strip_tac >>
  `val_in_memory tv v d actual.vs_memory` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_path ctx func initial gas_count (OK endpoint)` >>
  `abi_scratch_effect first last start.cs_next_id end_st.cs_next_id start.cs_next_var
    limit_st d (abi_decode_bytes_copy_size n) b cap initial endpoint` by
    (irule abi_scratch_leaf_effect >>
     fs[Abbr `endpoint`, fresh_vars_wrt_def, abi_decode_frame_def, eval_op_inst_idx] >>
     first_assum ACCEPT_TAC) >>
  qexistsl_tac [`endpoint`, `gas_count`] >>
  fs[Abbr `endpoint`] >> first_assum ACCEPT_TAC
QED

Theorem intcall_scratch_decoder_counted_base:
  intcall_scratch_decoder_counted ce env sf (BaseT bt) tv
Proof
  mp_tac (Q.SPEC `bt` abi_scratch_decoder_base_shape) >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `clamp` assume_tac)
    (qx_choose_then `n` assume_tac))
  >- (irule intcall_scratch_decoder_counted_word >> qexists_tac `clamp` >>
      asm_simp_tac bool_ss []) >>
  irule intcall_scratch_decoder_counted_bytestring >> qexists_tac `n` >>
  asm_simp_tac (srw_ss()) []
QED

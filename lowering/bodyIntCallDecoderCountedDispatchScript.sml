(* Total counted physical member execution, including empty dynamic descriptors. *)
Theory bodyIntCallDecoderCountedDispatch
Ancestors
  bodyIntCallDecoderCountedBody bodyIntCallDecoderCountedContract bodyIntCallDecoderCountedEmpty
  abiScratchDecoderMemberCons abiScratchDecoderContract abiScratchEncoderContract
  abiScratchDecoderRanges abiDecoderOffsetHead abiDecoderOffset
  abiScratchAddress abiDecoderCoherence abiDecoderEmpty abiDecoderContract
  abiDecoderTypedContract abiDecoderLoop abiDecoderReentry abiDecodeRanges
  abiEncoder fragGasPath fragExec compileEnv valueEncoding vyperABI contractABI
  venomState venomExecSemantics words list arithmetic

Theorem intcall_scratch_decoder_member_body_path:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc base_op hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc base_op hi (type_to_abi_dec_info sf ce ty)
    ready = ((),end_st) /\ fn_has_code st end_st func /\
  (ready.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  intcall_scratch_decoder_counted ce env sf ty tv /\ abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_scratch_decoder_ranges opc base_op hi src dst B sb (LENGTH bs) d outsz first last b cap initial /\
  mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_operand_live st.cs_next_var base_op /\ (base_op = Lit 0w \/ opc = MLOAD) /\
  abi_decoder_budget first last b cap initial /\ first <= abi_decoder_entry_floor st /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. val_in_memory tv v (d + vo) actual.vs_memory /\
    abi_scratch_effect first last (abi_decoder_entry_floor st) end_st.cs_next_id st.cs_next_var
      limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (drule_all abi_scratch_decoder_ranges_point >> strip_tac >>
      mp_tac (SIMP_RULE bool_ss [LET_THM]
        (Q.INST [`middle` |-> `ready`, `b` |-> `initial.vs_alloca_next`, `cap` |-> `0:num`]
          intcall_decoder_valid_empty_member_path)) >>
      impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
      `abi_scratch_effect first last (abi_decoder_entry_floor st) end_st.cs_next_id st.cs_next_var
        limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual` by
        (drule_all abi_scratch_address_effect >> simp[]) >>
      qexistsl_tac [`actual`, `n`] >> asm_simp_tac bool_ss []) >>
  `(is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)` by
    (strip_tac >> drule_all abi_decoder_nonempty_readable_head >> simp[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by
    simp[abi_decoder_needs_offset_iff] >>
  qpat_x_assum `dec_info_needs_offset _ = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] intcall_scratch_decoder_member_body_helper_path) >> simp[]
QED

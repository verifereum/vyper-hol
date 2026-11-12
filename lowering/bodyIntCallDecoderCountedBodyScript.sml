(* Compose counted address setup and a physical recursive child execution. *)
Theory bodyIntCallDecoderCountedBody
Ancestors
  bodyIntCallDecoderCountedContract bodyIntCallDecoderCountedInput
  abiScratchDecoderContract abiScratchEncoderContract abiScratchAfterAddress
  abiDecoderMemberBody abiDecoderDynamic abiDecoderAllocation abiDecoderLoop
  abiDecoderCoherence abiDecoderTypedContract abiDecoderContract abiDecoderReentry
  abiValidMember abiEncoder fragGasPath fragExec compileEnv valueEncoding
  vyperABI contractABI venomState venomExecSemantics words list arithmetic

Theorem intcall_scratch_decoder_member_body_helper_path:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc base_op hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc base_op hi (type_to_abi_dec_info sf ce ty)
    ready = ((),end_st) /\ fn_has_code st end_st func /\
  (ready.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  intcall_scratch_decoder_counted ce env sf ty tv /\ abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
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
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all abi_decoder_member_body_code >> strip_tac >>
  `first <= ready.cs_next_id /\ ready.cs_next_var <= limit_st.cs_next_var /\
   abi_decoder_entry_floor st <= ready.cs_next_id` by
    (fs[abi_decoder_entry_floor_def] >> decide_tac) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] intcall_scratch_decoder_member_entry_path) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func initial n (OK prepared)` >>
  `abi_decoder_budget first last b cap prepared` by fs[abi_scratch_effect_def] >>
  `first <= abi_decoder_entry_floor ready` by simp[abi_decoder_entry_floor_def] >>
  qhdtm_x_assum `intcall_scratch_decoder_counted`
    (drule_all o PURE_REWRITE_RULE [intcall_scratch_decoder_counted_def]) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `val_in_memory tv v (d + vo) actual.vs_memory` >>
  `abi_scratch_effect first last (abi_decoder_entry_floor st) end_st.cs_next_id st.cs_next_var limit_st
    (d + vo) (type_memory_bytes ce ty) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qexistsl_tac [`d + vo`, `end_st.cs_next_id`, `ready.cs_next_id`,
       `ready.cs_next_var`, `type_memory_bytes ce ty`, `prepared`] >>
     asm_simp_tac arith_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  metis_tac[gas_path_then]
QED

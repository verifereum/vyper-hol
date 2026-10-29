(* The real member prefix establishes the actual-source recursive input API. *)
Theory abiDecoderValidMemberInput
Ancestors
  abiDecoderValidContract abiValidMember abiValidMembers abiValidAggregateHeads
  abiDecoderMemberSetup abiDecoderReentry abiDecoderCoherence abiDecoderTypedContract
  abiDecoderContract abiDecodeRanges abiEncoder fragExec compileEnv valueEncoding vyperABI
  contractABI venomState venomExecSemantics words list arithmetic

Theorem abi_decoder_valid_member_readable:
  valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) ==>
  abi_member_head_size at <= LENGTH
    (abi_decode_member_bytes at bs (DROP (SUM (MAP abi_member_head_size pre)) bs))
Proof
  strip_tac >> drule abi_valid_member_head >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  Cases_on `is_dynamic at`
  >- (qpat_x_assum `valid_enc at _` mp_tac >>
      asm_simp_tac bool_ss [abi_decode_member_bytes_def] >> strip_tac >>
      `!elem. at <> Array (SOME 0) elem` by metis_tac[] >>
      drule_all abi_valid_dynamic_head_min >>
      asm_simp_tac bool_ss [abi_member_head_size_def, abi_decode_member_bytes_def]) >>
  `static_length at <= LENGTH (DROP (SUM (MAP abi_member_head_size pre)) bs)` by
    (qpat_x_assum `_ + abi_member_head_size at <= _` mp_tac >>
     asm_simp_tac bool_ss [abi_member_head_size_def] >> strip_tac >>
     simp[LENGTH_DROP] >> decide_tac) >>
  asm_simp_tac (srw_ss()) [abi_member_head_size_def, abi_decode_member_bytes_def, LENGTH_TAKE_EQ]
QED

Theorem abi_decoder_valid_member_entry:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,ready) /\ fn_has_code st ready func /\
  abi_decoder_coherent ce env sf ty tv /\
  valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared. abi_decoder_valid_pre ce env sf ty tv childbs v ready
      (FST ops) (SND ops) opc hi (sb + off) (d + vo) b cap prepared /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    abi_decode_sim ctx func initial prepared
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_valid_member_entry) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_decoder_valid_member_readable >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var` by simp[] >>
  `abi_decoder_operand_live ready.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  qexists_tac `prepared` >>
  asm_simp_tac bool_ss [abi_decoder_valid_pre_def, abi_decoder_head_window]
QED

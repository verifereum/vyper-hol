(* Physical recursive child inputs on the counted address-setup endpoint. *)
Theory bodyIntCallDecoderCountedInput
Ancestors
  bodyIntCallDecoderCountedMember abiScratchDecoderContract abiScratchDecoderRanges
  abiScratchDecoderSubwindow abiScratchDecoderTransport abiScratchAddress
  abiScratchEncoderContract abiDecoderValidMemberCons abiValidMember abiValidMembers
  abiValidDecodedMetadata abiDecoderMemberSetup abiDecoderDynamic abiDecoderCoherence
  abiDecoderTypedContract abiDecoderValidContract abiDecoderContract abiDecoderReentry abiDecoderLoop
  abiDecodeRanges abiEncoder abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs
  fragGasPath fragExec compileEnv valueEncoding vyperABI contractABI venomState
  words list arithmetic

Theorem intcall_scratch_decoder_member_entry_path:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc base_op hi
    (abi_decoder_dynamic (type_to_abi_dec_info (sf:string |-> (string # vyperAST$type # num) list) ce ty))
    ao vo st = (ops,ready) /\ fn_has_code st ready func /\
  abi_decoder_coherent ce env sf ty tv /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_scratch_decoder_ranges opc base_op hi src dst B sb (LENGTH bs) d outsz first last b cap initial /\
  mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_budget first last b cap initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_operand_live st.cs_next_var base_op /\ (base_op = Lit 0w \/ opc = MLOAD) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?prepared n. abi_scratch_decoder_input ce env sf ty tv childbs v ready
      (FST ops) (SND ops) opc base_op hi B (sb + off) (d + vo) first last b cap prepared /\
    abi_scratch_effect first last st.cs_next_id ready.cs_next_id st.cs_next_var
      limit_st d outsz b cap initial prepared /\
    fresh_vars_wrt limit_st prepared /\ abi_decoder_address_frame st.cs_next_var initial prepared /\
    prepared.vs_current_bb = ready.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~prepared.vs_halted /\
    gas_path ctx func initial n (OK prepared)
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_coherent_dynamic >> strip_tac >>
  qhdtm_assum `abi_scratch_decoder_ranges`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  drule_all abi_valid_member_window >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_valid_decoded_metadata >> strip_tac >>
  `is_dynamic (vyper_to_abi_type env ty) ==>
    eval_operand base_op initial = SOME (n2w B) /\
    abi_decode_load opc (n2w (B + (sb + SUM (MAP abi_member_head_size pre))):bytes32) initial =
      n2w (abi_decode_member_offset (vyper_to_abi_type env ty) bs (SUM (MAP abi_member_head_size pre))) /\
    sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre)) < dimword (:256)` by
    (strip_tac >> asm_simp_tac bool_ss [ADD_ASSOC] >> decide_tac) >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule_all intcall_decoder_member_setup_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path ctx func initial n (OK prepared)` >>
  `eval_operand (FST ops) prepared = SOME (n2w (sb +
    abi_decode_member_offset (vyper_to_abi_type env ty) bs (SUM (MAP abi_member_head_size pre))))` by
    (Cases_on `is_dynamic (vyper_to_abi_type env ty)` >>
     gvs[abi_decode_member_offset_def, Excl "vyper_decode_valid_enc_def", Excl "dec_def", Excl "enc_def"]) >>
  `abi_scratch_effect first last st.cs_next_id ready.cs_next_id st.cs_next_var
    limit_st d outsz b cap initial prepared` by
    (irule abi_scratch_address_effect >> asm_simp_tac bool_ss []) >>
  drule_all abi_scratch_decoder_ranges_effect >> strip_tac >>
  drule_all abi_decoder_address_frame_source >> disch_then (qspec_then `opc` assume_tac) >>
  drule_all abi_decoder_valid_member_readable >> strip_tac >>
  drule abi_decode_member_setup_counters >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var` by simp[] >>
  `abi_decoder_operand_live ready.cs_next_var hi /\
   abi_decoder_operand_live ready.cs_next_var base_op` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  qexistsl_tac [`prepared`, `n`] >>
  asm_simp_tac bool_ss [abi_scratch_decoder_input_def, abi_decoder_head_window, ADD_ASSOC] >>
  irule abi_scratch_decoder_subwindow_ranges >> asm_simp_tac bool_ss [] >>
  qexistsl_tac [`d`, `dst`, `LENGTH (bs:word8 list)`, `outsz`, `sb`, `src`] >>
  asm_simp_tac arith_ss []
QED

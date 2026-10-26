(* Execute the actual member prefix and recursive child under physical scratch ownership. *)
Theory abiScratchDecoderMemberBody
Ancestors
  abiScratchDecoderContract abiScratchDecoderMemberEntry abiScratchEncoderContract
  abiScratchDecoderRanges abiScratchAddressEffect abiDecoderEmptyMember
  abiDecoderOffset abiDecoderOffsetHead
  abiScratchAfterAddress abiDecoderMemberBody abiDecoderMemberSetup abiDecoderArrayBody
  abiDecoderDynamicLoopSetup abiDecoderArrayInitExec abiDecoderAllocation
  abiDecoderCoherence abiDecoderDynamic abiDecoderTypedContract abiDecoderContract
  abiDecoderReentry abiDecoderLoop abiDecodeRanges abiEncoder fragExec compileEnv
  valueEncoding vyperABI contractABI venomState venomExecSemantics words list arithmetic

Theorem abi_scratch_decoder_member_body_helper:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc hi (abi_decoder_dynamic (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi (type_to_abi_dec_info sf ce ty)
    ready = ((),end_st) /\ fn_has_code st end_st func /\
  (ready.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder ce env sf ty tv /\ abi_decoder_coherent ce env sf ty tv /\
  valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + vo) actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode opc` by fs[abi_scratch_decoder_ranges_def] >>
  drule_all abi_decoder_member_body_code >> strip_tac >>
  `first <= ready.cs_next_id /\ ready.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM] abi_scratch_decoder_member_entry) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  `abi_decoder_budget first last b cap prepared` by fs[abi_scratch_effect_def] >>
  qhdtm_x_assum `abi_scratch_decoder` (mp_tac o PURE_REWRITE_RULE [abi_scratch_decoder_def]) >>
  disch_then (qspecl_then [`SND (ops:operand # operand)`, `FST (ops:operand # operand)`,
    `opc`, `hi`, `ready`, `end_st`, `func`, `ctx`, `first`, `last`, `b`, `cap`,
    `limit_st`, `prepared:venom_state`,
    `abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (SUM (MAP abi_member_head_size pre)) bs)`, `v`,
    `sb + abi_decode_member_offset (vyper_to_abi_type env ty) bs
      (SUM (MAP abi_member_head_size pre))`, `d + vo`] mp_tac) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `val_in_memory tv v (d + vo) actual.vs_memory` >>
  `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + vo) (type_memory_bytes ce ty) b cap initial actual` by
    (irule abi_scratch_effect_after_address >>
     qexistsl_tac [`d + vo`, `end_st.cs_next_id`, `ready.cs_next_id`,
       `ready.cs_next_var`, `type_memory_bytes ce ty`, `prepared`] >>
     asm_simp_tac arith_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_member_body:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      off = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,ready) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc hi (type_to_abi_dec_info sf ce ty)
    ready = ((),end_st) /\ fn_has_code st end_st func /\
  (ready.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_decoder ce env sf ty tv /\ abi_decoder_coherent ce env sf ty tv /\
  valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_scratch_decoder_ranges opc hi src dst sb (LENGTH bs) d outsz first last b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source opc initial) = bs /\
  vo + type_memory_bytes ce ty <= outsz /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv v (d + vo) actual.vs_memory /\
    abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
      limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  Cases_on `type_to_abi_dec_info sf ce ty = DecComplex T []`
  >- (drule_all abi_scratch_decoder_ranges_point >> strip_tac >>
      mp_tac (SIMP_RULE bool_ss [LET_THM]
        (Q.INST [`middle` |-> `ready`, `b` |-> `initial.vs_alloca_next`, `cap` |-> `0:num`]
          abi_decoder_valid_empty_member)) >>
      impl_tac >- asm_simp_tac bool_ss [] >>
      disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
      `abi_scratch_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var
        limit_st (d + vo) (type_memory_bytes ce ty) b cap initial actual` by
        (drule_all abi_scratch_address_effect >> simp[]) >>
      qexists_tac `actual` >> asm_simp_tac bool_ss []) >>
  `(is_dynamic (vyper_to_abi_type env ty) ==>
    !elem. vyper_to_abi_type env ty <> Array (SOME 0) elem)` by
    (strip_tac >> drule_all abi_decoder_nonempty_readable_head >> simp[]) >>
  `dec_info_needs_offset (type_to_abi_dec_info sf ce ty) =
    abi_decoder_dynamic (type_to_abi_dec_info sf ce ty)` by
    simp[abi_decoder_needs_offset_iff] >>
  qpat_x_assum `dec_info_needs_offset _ = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] abi_scratch_decoder_member_body_helper) >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_SCRATCH_DECODER_MEMBER_BODY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI physical member body not kernel closed: " ^ n)
  end) (DB.thms "abiScratchDecoderMemberBody");


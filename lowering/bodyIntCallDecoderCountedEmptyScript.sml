(* Counted guard and inline-head execution for empty decoder members. *)
Theory bodyIntCallDecoderCountedEmpty
Ancestors
  bodyIntCallDecoderCountedMember bodyIntCallDecoderCountedPrimitive
  abiDecoderComplexGuard abiDecoderComplexHead abiDecoderEmpty abiDecoderEmptyMember
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract
  abiDecoderTypedContract abiDecoderCoherence abiDecoderLoop abiValidMember abiValidMembers
  abiDecodeRanges abiEncoder fragGasPath fragExec exprLoweringProps emitHelperProps
  compileEnv venomState venomInst venomExecSemantics instIdxIndep entrySinkExtraction
  words list rich_list arithmetic

Theorem intcall_decoder_complex_head_guard_path:
  abi_decode_complex_head_guard src hi head_sz st = ((),st') /\ fn_has_code st st' func /\
  eval_operand src initial = SOME (n2w sb) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + head_sz <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\
    actual.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_complex_guard_code >> strip_tac >>
  drule abi_decode_complex_head_guard_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all abi_decoder_complex_guard_reentry >> strip_tac >>
  drule_all intcall_same_block_seq_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  goal_assum (drule_at Any) >>
  gvs[fresh_vars_wrt_def, abi_decoder_address_frame_def, eval_op_inst_idx]
QED

Theorem intcall_decoder_empty_member_path:
  abi_decode_member_setup dst src opc base_op hi F ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc base_op hi (DecComplex dynamic [])
    middle = ((),end_st) /\ fn_has_code st end_st func /\ abi_decode_source_opcode opc /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  (hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + ao <= hb /\ hb < dimword (:256)) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ abi_decoder_operand_live st.cs_next_var base_op /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_empty_member_code >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`st'` |-> `middle`, `dyn` |-> `F`, `payload_off` |-> `0:num`,
    `s` |-> `initial:venom_state`]
    intcall_decoder_member_setup_path) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  strip_tac >>
  rename1 `gas_path ctx func initial n (OK prepared)` >>
  `abi_decoder_operand_live middle.cs_next_var hi` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all abi_decoder_address_frame_guard >> disch_then assume_tac >>

  `abi_decode_complex_head_guard (FST ops) hi 0 middle = ((),end_st)` by
    fs[abi_decode_empty_complex_phases] >>
  mp_tac (Q.INST [`st` |-> `middle`, `st'` |-> `end_st`,
    `src` |-> `FST (ops:operand # operand)`, `sb` |-> `sb + ao`, `head_sz` |-> `0:num`,
    `initial` |-> `prepared:venom_state`] intcall_decoder_complex_head_guard_path) >>
  impl_tac >- asm_simp_tac (srw_ss()) [] >> strip_tac >>
  rename1 `gas_path ctx func prepared n' (OK actual)` >>
  `abi_decoder_address_frame st.cs_next_var initial actual` by
    (irule abi_decoder_address_frame_trans >>
     qexistsl_tac [`middle.cs_next_var`, `prepared`] >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> metis_tac[gas_path_then]
QED

Theorem intcall_decoder_valid_empty_member_path:
  let at = vyper_to_abi_type env ty;
      ao = SUM (MAP abi_member_head_size pre);
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  abi_decode_member_setup dst src opc base_op hi (dec_info_needs_offset (type_to_abi_dec_info sf ce ty))
    ao vo st = (ops,middle) /\
  compile_abi_decode_to_buf (SND ops) (FST ops) opc base_op hi (type_to_abi_dec_info sf ce ty)
    middle = ((),end_st) /\ fn_has_code st end_st func /\
  abi_decoder_coherent ce env sf ty tv /\ type_to_abi_dec_info sf ce ty = DecComplex T [] /\
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  abi_to_vyper env ty (dec at childbs) = SOME v /\
  abi_decoder_ranges opc base_op hi src dst B sb (LENGTH bs) d outsz b cap initial /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ abi_decoder_operand_live st.cs_next_var base_op /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual n. val_in_memory tv v (d + vo) actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\
    abi_decoder_address_frame st.cs_next_var initial actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    gas_path ctx func initial n (OK actual)
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_empty_descriptor_value >> strip_tac >>
  drule abi_valid_member_head >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qhdtm_assum `abi_decoder_ranges`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  SUBGOAL_THEN ``hi = Lit 0w \/ ?hb. eval_operand hi initial = SOME (n2w hb) /\
    sb + SUM (MAP abi_member_head_size pre) <= hb /\ hb < dimword (:256)`` assume_tac
  >- (Cases_on `hi = Lit 0w` >- simp[] >>
      qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >> strip_tac >>
      rename1 `eval_operand hi initial = SOME (n2w hb)` >>
      qexists_tac `hb` >> asm_simp_tac arith_ss [] >> decide_tac) >>
  qpat_x_assum `type_to_abi_dec_info _ _ _ = DecComplex T []`
    (fn th => RULE_ASSUM_TAC (SIMP_RULE bool_ss [th, dec_info_needs_offset_def])) >>
  drule_all intcall_decoder_empty_member_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  goal_assum (drule_at Any) >> asm_simp_tac bool_ss []
QED

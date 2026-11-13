(* Memory checks for member navigation with stale decoder temporaries. *)
Theory abiDecodeMemMemberReentry
Ancestors
  abiDecodeMemMemberPointer abiDecodeMemSequenceReentry
  exprSimAbiDecodeMemberOutcome abiDecoderBytestringOutcome abiDecoderWordOutcome
  abiDecoderSiteEffect
  abiDecoderReentryPointer abiDecoderReentry abiDecoderContract abiDecoderBytesPrefix
  abiDecoderVarSequence abiDecoderVarExtend fragExecMem exprLoweringProps
  abiDecoderMemberSetup abiDecoderDynamicLoopSetup abiDecoderRange
  emitHelperProps compileEnv emitHelper context rich_list
  fragGasSeqMem fragGasSeqAbort fragGasMode entryDecoderHistoryFrame
  entrySinkExtraction allocaHistoryFragment bodyUnopFragMemory
  entryDecoderSetupEndpoint
  loweringStateRelDefs venomExecSemantics venomState venomInst words arithmetic list

Theorem abi_decode_member_reentry_mem_ok[local]:
  compile_getelemptr_abi src dyn off MLOAD bop hi st = (member_op,last) /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  sb < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var bop /\
  (dyn ==> eval_operand bop s = SOME (n2w B) /\
    B+sb+off < dimword (:256) /\ B+sb+off+32 <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts st last) s
Proof
  strip_tac >> qabbrev_tac `clean = abi_decoder_prune_vars st.cs_next_var s` >>
  `eval_operand src clean = SOME (n2w sb) /\ fresh_vars_wrt st clean` by
    simp[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_fresh] >>
  `dyn ==> eval_operand bop clean = SOME (n2w B) /\
    B+sb+off < dimword (:256) /\ B+sb+off+32 <= clean.vs_alloca_next` by
    (strip_tac >> fs[Abbr `clean`, abi_decoder_prune_eval,
      abi_decoder_prune_vars_def] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts st last) clean` by
    (irule abi_decode_mem_member_safe >> metis_tac[]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_pointer_code >> strip_tac >>
  `abi_decoder_vars_extend s.vs_vars clean s` by
    simp[Abbr `clean`, abi_decoder_prune_extension] >>
  MATCH_MP_TAC (Q.SPECL [`emitted_insts st last`, `s.vs_vars`, `clean`, `s`]
    abi_decode_sequence_mem_extend) >> asm_rewrite_tac[] >>
  Cases_on `dyn /\ dimword (:256) <= sb + w2n (mload (B+sb+off) clean)`
  >- (disj2_tac >> irule abi_decode_mem_member_rejected >> asm_rewrite_tac[] >>
      qexistsl_tac [`B`,`bop`,`hi`,`member_op`,`off`,`sb`,`src`] >> fs[]) >>
  disj1_tac >>
  `dyn ==> eval_operand bop clean = SOME (n2w B) /\
     abi_decode_load MLOAD (n2w (B+(sb+off)):bytes32) clean =
     n2w (w2n (mload (B+sb+off) clean)) /\
     sb + w2n (mload (B+sb+off) clean) < dimword (:256)` by
    (strip_tac >> fs[] >> pure_rewrite_tac[abi_decode_load_def] >>
     asm_simp_tac std_ss [w2n_n2w, n2w_w2n, LESS_MOD, ADD_ASSOC]) >>
  drule_all abi_decoder_member_pointer_sequence >> strip_tac >> metis_tac[]
QED

Theorem abi_decode_member_setup_old_outputs[local]:
  abi_decode_member_setup dst src MLOAD bop hi dyn ao vo st = (ops,last) /\
  not_fresh_at st x ==>
  EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts st last)
Proof
  Cases_on `dyn` >> Cases_on `hi = Lit 0w` >> Cases_on `bop = Lit 0w` >>
  simp[abi_decode_member_setup_def, abiEncoderTheory.compile_getelemptr_abi_def,
    abiEncoderTheory.compile_abi_dec_addr_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def] >>
  fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]
QED

Theorem abi_decode_member_setup_reentry_mem_ok[local]:
  abi_decode_member_setup dst src MLOAD bop hi dyn ao vo st = (ops,last) /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  sb < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var bop /\
  (dyn ==> eval_operand bop s = SOME (n2w B) /\
    B+sb+ao < dimword (:256) /\ B+sb+ao+32 <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts st last) s
Proof
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src dyn ao MLOAD bop hi st = (child_src,mid)` >>
  rename1 `emit_op ADD [dst; Lit (n2w vo)] mid = (child_dst,last)` >>
  drule abi_decode_mem_member_shape >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `emitted_insts st last = emitted_insts st mid ++ emitted_insts mid last` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st mid) s` by
    (irule abi_decode_member_reentry_mem_ok >>
     qexistsl_tac [`B`,`bop`,`dyn`,`hi`,`child_src`,`ao`,`sb`,`src`] >>
     asm_rewrite_tac[] >> strip_tac >>
     qpat_x_assum `dyn ==> _` mp_tac >>
     asm_rewrite_tac[] >> strip_tac >> asm_rewrite_tac[] >> decide_tac) >>
  asm_rewrite_tac[] >> MATCH_MP_TAC run_inst_seq_mem_ok_append >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  simp[run_inst_seq_mem_ok_last, mk_inst_def,
    instMemFrontierTheory.below_frontier_no_ranges,
    memSafeRunTheory.inst_dload_in_section_other]
QED

Theorem abi_decode_member_setup_reentry_path_mem:
  abi_decode_member_setup dst src MLOAD bop hi dyn ao vo st = (ops,last) /\
  hi <> Lit 0w /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ sb < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var bop /\
  abi_decoder_operand_live st.cs_next_var hi /\
  last.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  (dyn ==> eval_operand bop s = SOME (n2w B) /\
    B+sb+ao < dimword (:256) /\ B+sb+ao+32 <= s.vs_alloca_next) /\
  fn_has_code st last func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ((dyn ==> sb + w2n (mload (B+sb+ao) s) < dimword (:256)) ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand (FST ops) t = SOME
        (n2w (sb + if dyn then w2n (mload (B+sb+ao) s) else ao)) /\
      eval_operand (SND ops) t = SOME (n2w (d+vo)) /\
      t.vs_current_bb = last.cs_current_bb /\
      t.vs_inst_idx = LENGTH last.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt limit_st t /\ decode_static_frame s t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
      t.vs_data_section = s.vs_data_section /\
      t.vs_alloca_next = s.vs_alloca_next /\ t.vs_allocas = s.vs_allocas /\
      alloca_history func t) /\
  (dyn /\ dimword (:256) <= sb + w2n (mload (B+sb+ao) s) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >> drule abi_decode_member_mload_setup_shape >> strip_tac >>
  `isPREFIX st.cs_current_insts last.cs_current_insts` by fs[inst_extends_def] >>
  `run_inst_seq_mem_ok (emitted_insts st last) s` by
    (irule abi_decode_member_setup_reentry_mem_ok >>
     qexistsl_tac [`B`,`ao`,`bop`,`dst`,`dyn`,`hi`,`ops`,`sb`,`src`,`vo`] >>
     asm_rewrite_tac[]) >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st last) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st last)) = 0` by
    (fs[EVERY_MEM, FILTER_EQ_NIL] >> rpt strip_tac >> res_tac >>
     gvs[abi_bytes_opcode_def, abi_word_opcode_def]) >>
  conj_tac >- suspend "accept" >> suspend "reject"
QED
Resume abi_decode_member_setup_reentry_path_mem[accept]:
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `dyn ==> eval_operand bop s = SOME (n2w B) /\
    abi_decode_load MLOAD (n2w (B+(sb+ao)):bytes32) s =
    n2w (w2n (mload (B+sb+ao) s)) /\
    sb + w2n (mload (B+sb+ao) s) < dimword (:256)` by
    (strip_tac >> fs[] >>
     `B+(sb+ao) < dimword (:256)` by decide_tac >>
     pure_rewrite_tac[abi_decode_load_def] >>
     asm_simp_tac std_ss [w2n_n2w, n2w_w2n, ADD_ASSOC, LESS_MOD]) >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st last) s = OK u` >>
  `decode_static_frame s u` by
    (drule abi_decode_member_mload_setup_shape >> strip_tac >>
     `EVERY (\i. abi_bytes_opcode i.inst_opcode) (emitted_insts st last)`
       by fs[EVERY_MEM] >>
     drule_all abi_bytes_sequence_static >>
     simp[decode_static_frame_def, venom_state_component_equality]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st last) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st last)` by
    fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all entry_sequence_nonterminator_labels >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op u = eval_operand op s` by
    (Cases >> simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      eval_operand_def] >> strip_tac >>
     rename1 `lookup_var name u = lookup_var name s` >>
     `not_fresh_at st name` by fs[not_fresh_at_def] >>
     irule entry_sequence_nonoutput_lookup >>
     qexists_tac `emitted_insts st last` >> simp[] >>
     drule_all abi_decode_member_setup_old_outputs >> fs[EVERY_MEM]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts st last) = LENGTH last.cs_current_insts` by
    (gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  qexists_tac `u with vs_inst_idx := LENGTH last.cs_current_insts` >>
  gvs[instMemFrontierTheory.eval_operand_inst_idx, fresh_vars_wrt_def,
    abi_decoder_address_frame_def, decode_static_frame_def,
    venom_state_component_equality]
QED
Resume abi_decode_member_setup_reentry_path_mem[reject]:
  strip_tac >> gvs[] >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [abi_decode_member_setup_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src T ao MLOAD bop hi st = (child_src,mid)` >>
  rename1 `emit_op ADD [dst; Lit (n2w vo)] mid = (child_dst,last)` >>
  drule abi_decode_mem_member_shape >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `emitted_insts st last = emitted_insts st mid ++ emitted_insts mid last` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qabbrev_tac `clean = abi_decoder_prune_vars st.cs_next_var s` >>
  `fresh_vars_wrt st clean /\ eval_operand src clean = SOME (n2w sb) /\
   eval_operand bop clean = SOME (n2w B) /\
   mload (B+sb+ao) clean = mload (B+sb+ao) s` by
    simp[Abbr `clean`, abi_decoder_prune_eval, abi_decoder_prune_fresh,
      abi_decoder_prune_vars_def, mload_def] >>
  `?u. run_inst_seq (emitted_insts st mid) clean = Abort Revert_abort u` by
    (irule abi_decode_mem_member_rejected >> asm_rewrite_tac[] >>
     qexistsl_tac [`B`,`bop`,`hi`,`child_src`,`ao`,`sb`,`src`] >> simp[]) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_member_pointer_code >> strip_tac >>
  `abi_decoder_vars_extend s.vs_vars clean s` by
    simp[Abbr `clean`, abi_decoder_prune_extension] >>
  drule_all abi_decode_sequence_revert_extend >> strip_tac >>
  `?u. run_inst_seq (emitted_insts st last) s = Abort Revert_abort u` by
    (asm_rewrite_tac[] >> simp[run_inst_seq_append_err] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts st last)` by
      (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st last) (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >> metis_tac[]
QED
Finalise abi_decode_member_setup_reentry_path_mem

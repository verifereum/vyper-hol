(* Bounded offset loads in the actual complex-member setup. *)
Theory extcallDecoderMemberPreparationMemory
Ancestors
  abiDecoderContract abiDecoderMemberSetup abiDecoderMemberCode abiDecoderReentry abiDecoderReentryAddress
  abiDecoderArrayBackedge abiEncoder compileEnv emitHelper emitHelperProps exprLoweringProps
  ssaOperandFrame fragExecMem fragGasSeqMem fragGasPathMem instMemFrontier
  venomInstProofs venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem extcall_decoder_member_setup_mem_ok:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,st') /\
  eval_operand src s = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  (dyn ==> eval_operand base_op s = SOME (n2w B) /\
    B+sb+ao < dimword(:256) /\ B+sb+ao+32 <= s.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  strip_tac >>
  `!k. st.cs_next_var <= k ==> base_op <> Var (STRING #"%" (toString k))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  Cases_on `dyn` >> Cases_on `base_op = Lit 0w` >> Cases_on `hi = Lit 0w` >>
  qpat_x_assum `abi_decode_member_setup _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_member_setup_def, compile_getelemptr_abi_def,
       compile_abi_dec_addr_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND] >>
  simp[run_inst_seq_mem_ok_every, below_frontier_no_ranges,
       memSafeRunTheory.inst_dload_in_section_def, mk_inst_def] >>
  (qmatch_goalsub_abbrev_tac `run_inst_seq_mem_ok code s` >>
  `code = TAKE (if (EL 1 code).inst_opcode = MLOAD then 2 else 3) code ++
          DROP (if (EL 1 code).inst_opcode = MLOAD then 2 else 3) code` by simp[] >>
  pop_assum (fn th => pure_once_rewrite_tac[th]) >>
  match_mp_tac run_inst_seq_mem_ok_append >> reverse conj_tac
  >- (rpt strip_tac >> irule run_inst_seq_mem_ok_every >>
      simp[Abbr `code`, below_frontier_no_ranges, memSafeRunTheory.inst_dload_in_section_def]) >>
  simp[Abbr `code`, run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last,
       below_frontier_no_ranges, GSYM mk_inst_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_update_var_avoids, eval_operand_def, lookup_var_update_var,
       word_add_n2w] >>
  simp[GSYM mk_inst_def, below_frontier_MLOAD, eval_operand_def,
       lookup_var_update_var, w2n_n2w] >>
  simp[lookup_var_update_var, w2n_n2w] >>
  rpt strip_tac >> gvs[update_var_def] >> decide_tac)
QED

Theorem extcall_decoder_member_setup_success:
  abi_decode_member_setup dst src MLOAD base_op hi dyn ao vo st = (ops,st') /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (dyn ==> eval_operand base_op s = SOME (n2w B) /\
    abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w payload_off /\
    sb+payload_off < dimword(:256) /\ B+sb+ao < dimword(:256) /\
    B+sb+ao+32 <= s.vs_alloca_next) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t. gas_path_mem ctx func s
        (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')))
        (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
      eval_operand (FST ops) t = SOME (n2w (sb + if dyn then payload_off else ao)) /\
      eval_operand (SND ops) t = SOME (n2w (d+vo)) /\
      abi_decoder_operand_live st'.cs_next_var (FST ops) /\
      abi_decoder_operand_live st'.cs_next_var (SND ops) /\
      fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
      inst_extends st st' /\ t.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (irule extcall_decoder_member_setup_mem_ok >> metis_tac[]) >>
  `dyn ==> eval_operand base_op s = SOME (n2w B) /\
    abi_decode_load MLOAD (n2w (B+(sb+ao)) : bytes32) s = n2w payload_off /\
    sb+payload_off < dimword(:256)` by metis_tac[] >>
  drule_all abi_decode_member_setup_reentry >> strip_tac >>
  drule_all abi_decode_member_setup_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_CONJ] >>
  drule_all run_inst_seq_gas_path_mem >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    metis_tac[fragExecTheory.exec_block_run_inst_seq] >>
  qexists_tac `t` >> simp[ADD_COMM]
QED

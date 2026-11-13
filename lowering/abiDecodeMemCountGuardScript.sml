Theory abiDecodeMemCountGuard
Ancestors
  abiDecoderReentry appendStorageStageTransportPtr stmtReasonMemory
  abiDecoderGuards abiDecoderContract abiDecoderRange abiDecoderBytesPrefix
  emitHelperProps exprLoweringProps emitHelper compileEnv loweringStateRelDefs
  fragExec fragExecMem fragGasSeqMem fragGasSeqAbort bodyUnopFragMemory entrySinkExtraction
  allocaHistoryFragment entryDecoderHistoryFrame instMemFrontier allocaFootprint memSafeRun
  venomExecSemantics venomExecProofs venomInst venomState words arithmetic list rich_list

Theorem abi_decode_mload_count_rejected[local]:
  abi_decode_count_guard MLOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\ limit < dimword (:256) /\
  limit < w2n (abi_decode_load MLOAD p s) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[w2n_n2w, bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]
QED

Theorem abi_decode_mload_count_mem_ok[local]:
  abi_decode_count_guard MLOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND] >>
  simp[Once run_inst_seq_mem_ok_def] >>
  conj_tac >- simp[below_frontier_MLOAD] >>
  Cases_on `step_inst_base (mk_inst st.cs_next_id MLOAD [src]
    [STRING #"%" (toString st.cs_next_var)]) s` >> simp[] >>
  irule run_inst_seq_mem_ok_every >>
  simp[mk_inst_def, inst_dload_in_section_def] >>
  rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >> simp[]
QED

Theorem abi_decode_mload_count_opcodes[local]:
  abi_decode_count_guard MLOAD src limit st = (count_op,st') ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem abi_decode_mload_count_path_mem:
  abi_decode_count_guard MLOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\ w2n p + 32 <= s.vs_alloca_next /\
  limit < dimword (:256) /\ fresh_vars_wrt st s /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (w2n (abi_decode_load MLOAD p s) <= limit ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\
      eval_operand count_op t = SOME (abi_decode_load MLOAD p s) /\
      t.vs_current_bb = st'.cs_current_bb /\
      t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op s) /\
      t.vs_memory = s.vs_memory /\
      t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_allocas = s.vs_allocas /\ alloca_history func t) /\
  (limit < w2n (abi_decode_load MLOAD p s) ==>
    ?t. gas_marked_path T ctx func s 0 (Abort Revert_abort t))
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_count_guard_fragment_shape >> strip_tac >>
  drule abi_decode_mload_count_opcodes >> strip_tac >>
  drule_all abi_decode_mload_count_mem_ok >> strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0`
    by (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  conj_tac >- suspend "accept" >> suspend "reject"
QED
Resume abi_decode_mload_count_path_mem[accept]:
  strip_tac >>
  `abi_decode_load MLOAD p s = n2w (w2n (abi_decode_load MLOAD p s))` by simp[] >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all abi_decode_nonallocating_sequence_frame >> strip_tac >>
  `!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >> irule run_inst_seq_non_output_vars >>
     qexists_tac `emitted_insts st st'` >> simp[] >>
     qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def] >>
     fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL, LESS_EQ_ADD]) >>
  `t.vs_labels = s.vs_labels` by metis_tac[run_inst_seq_data_section] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (Cases >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      eval_operand_def, not_fresh_at_def]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by (gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> gvs[fresh_vars_wrt_def]
QED
Resume abi_decode_mload_count_path_mem[reject]:
  strip_tac >> drule_all abi_decode_mload_count_rejected >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_abort_zero_path_mem >> strip_tac >> metis_tac[]
QED
Finalise abi_decode_mload_count_path_mem

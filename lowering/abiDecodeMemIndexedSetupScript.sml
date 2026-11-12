(* Actual-state paths for array payload address arithmetic. *)
Theory abiDecodeMemIndexedSetup
Ancestors
  calldataDynOwned calldataDynStep abiDecoderIndexedAddress
  abiDecodeMemElementReentry entrySinkExtraction entryDecoderHistoryFrame
  fragGasSeqMem fragExecMem fragExec compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomState venomInst words list rich_list
  allocaFootprint abiDecoderReentry

Theorem abi_decode_indexed_address_path_mem:
  abi_decode_indexed_address base_op idx stride st = (address,st') /\
  eval_operand base_op s = SOME (n2w sb) /\ eval_operand idx s = SOME (n2w j) /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  abi_decoder_operand_live st.cs_next_var idx /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand address t = SOME (n2w (sb+32+j*stride)) /\
    abi_decoder_operand_live st'.cs_next_var address /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t
Proof
  strip_tac >> drule calldata_indexed_address_code_shape >> strip_tac >>
  drule_all calldata_indexed_address_repeat >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') s` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >>
     fs[EVERY_MEM] >>
     drule (GEN_ALL calldata_indexed_address_prefix_safe) >>
     disch_then (qspec_then `s` mp_tac) >> simp[APPEND_ASSOC]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0` by
    (qpat_x_assum `abi_decode_indexed_address _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_indexed_address_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
     simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')` by fs[EVERY_MEM] >>
  drule_all run_inst_seq_gas_path_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> gvs[]
QED

Theorem abi_decode_index_read_path_mem:
  emit_op MLOAD [ip] st = (idx,st') /\ eval_operand ip s = SOME p /\
  w2n p + 32 <= s.vs_alloca_next /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand idx t = SOME (mload (w2n p) s) /\
    abi_decoder_operand_live st'.cs_next_var idx /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t
Proof
  strip_tac >> drule_all calldata_mload_repeat >> strip_tac >>
  drule_all emit_mload_mem_ok >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_decoder_operand_live_emit >> strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\ st'.cs_blocks = st.cs_blocks` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
       comp_ignore_bind_def, comp_return_def, emit_def] >> strip_tac >> gvs[]) >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by fs[inst_extends_def] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st') /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0`
    by simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> gvs[]
QED

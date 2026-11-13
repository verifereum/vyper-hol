(* Actual-state paths for array payload address arithmetic. *)
Theory abiDecodeMemIndexedSetup
Ancestors
  calldataDynOwned calldataDynStep abiDecoderIndexedAddress
  abiDecodeMemElementReentry entrySinkExtraction entryDecoderHistoryFrame
  fragGasSeqMem fragExecMem fragExec compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomState venomInst words list rich_list
  allocaFootprint abiDecoderReentry abiDecoderStaticLoopSetup
  calldataFiniteTransport fragGasPathMem arithmetic

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

Theorem abi_decode_static_element_setup_path_mem:
  abi_decode_array_element_setup ip src dst opc bop hi di asz msz st = (ops,st') /\
  ~dec_info_needs_offset di /\ eval_operand ip s = SOME p /\
  mload (w2n p) s = n2w i /\ w2n p + 32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand (FST ops) t = SOME (n2w i) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb+32+i*asz)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d+32+i*msz)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t
Proof
  strip_tac >> drule_all abi_decode_static_element_setup_operands >> strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_static_element_setup_phases, comp_bind_def,
                       comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx,c1)` >>
  rename1 `abi_decode_indexed_address src idx asz c1 = (cs,c2)` >>
  rename1 `abi_decode_indexed_address dst idx msz c2 = (cd,end_st)` >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac abi_decode_indexed_address_counters >>
  imp_res_tac calldata_indexed_address_code_shape >>
  `cs_extends st c1` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def, emit_def,
          comp_ignore_bind_def, comp_return_def, cs_extends_def, IS_PREFIX_APPEND] >>
     strip_tac >> gvs[] >> simp[IS_PREFIX_APPEND]) >>
  `cs_extends c1 c2 /\ cs_extends c2 end_st` by
    (simp[cs_extends_def] >> metis_tac[]) >>
  `fn_has_code st c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 end_st func`
    by metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all abi_decode_index_read_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s 0 (OK s1)` >>
  suspend "addresses"
QED

Resume abi_decode_static_element_setup_path_mem[addresses]:
  `alloca_inv s1` by metis_tac[calldata_alloca_inv_fields] >>
  `abi_decoder_operand_live c1.cs_next_var src /\
   abi_decoder_operand_live c1.cs_next_var dst` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand src s1 = SOME (n2w sb) /\
   eval_operand dst s1 = SOME (n2w d) /\
   eval_operand idx s1 = SOME (n2w i)` by metis_tac[] >>
  drule_all abi_decode_indexed_address_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s1 0 (OK s2)` >>
  `alloca_inv s2` by metis_tac[calldata_alloca_inv_fields] >>
  `abi_decoder_operand_live c2.cs_next_var dst /\
   abi_decoder_operand_live c2.cs_next_var idx` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `c1.cs_next_var` >> simp[]) >>
  `eval_operand dst s2 = SOME (n2w d) /\
   eval_operand idx s2 = SOME (n2w i)` by metis_tac[] >>
  qpat_x_assum `abi_decode_indexed_address src _ _ _ = _` kall_tac >>
  drule_all abi_decode_indexed_address_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path_mem ctx func s2 0 (OK t)` >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (qpat_x_assum `gas_path_mem ctx func s 0 (OK s1)` mp_tac >>
     qpat_x_assum `gas_path_mem ctx func s1 0 (OK s2)` mp_tac >>
     qpat_x_assum `gas_path_mem ctx func s2 0 (OK t)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[gas_path_mem_then, ADD_CLAUSES]) >>
  `eval_operand idx t = SOME (n2w i) /\
   eval_operand cs t = SOME (n2w (sb+32+i*asz))` by metis_tac[] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op` by
       (conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [GSYM ADD_ASSOC] >>
  simp[MULT_COMM]
QED
Finalise abi_decode_static_element_setup_path_mem

(* Actual-state array head and guarded element preparation. *)
Theory abiDecodeMemArraySetup
Ancestors
  abiDecodeMemIndexedSetup abiDecodeMemElementReentry abiDecoderDynamicLoopSetup
  calldataDynOwned calldataDynStep entryDecoderHistoryFrame entrySinkExtraction
  fragGasSeqMem fragExecMem fragExec compileEnv emitHelper emitHelperProps
  exprLoweringProps venomExecSemantics venomState venomInst words list rich_list
  allocaFootprint abiDecoderReentry arithmetic abiDecoderIndexedAddress

Theorem abi_decode_coordinates_address[local]:
  abi_decode_indexed_coordinates src idx stride st = ((data,head),st') ==>
  abi_decode_indexed_address src idx stride st = (head,st')
Proof
  simp[abi_decode_indexed_coordinates_def, abi_decode_indexed_address_def,
       comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[]
QED

Theorem abi_decode_array_head_memory[local]:
  abi_decode_array_head_setup ip src asz st = ((idx,data,head),st') /\
  eval_operand ip s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> GAS) (emitted_insts st st') /\
  run_inst_seq_mem_ok (emitted_insts st st') s
Proof
  simp[abi_decode_array_head_setup_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MLOAD [ip] st = (idx,c1)` >>
  rename1 `abi_decode_indexed_coordinates src idx asz c1 = ((data,head),end_st)` >>
  drule abi_decode_coordinates_address >> strip_tac >>
  drule calldata_indexed_address_code_shape >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  `isPREFIX st.cs_current_insts c1.cs_current_insts` by simp[IS_PREFIX_APPEND] >>
  `emitted_insts st end_st = emitted_insts st c1 ++ emitted_insts c1 end_st` by
    (irule emitted_insts_append >> simp[] >>
     metis_tac[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  suspend "checks"
QED
Resume abi_decode_array_head_memory[checks]:
  `c1.cs_current_bb = st.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def, emit_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts c1 end_st)` by
    (qpat_x_assum `abi_decode_indexed_address _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_indexed_address_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[] >> simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND, mk_inst_def]) >>
  `!u. run_inst_seq_mem_ok (emitted_insts c1 end_st) u` by
    (gen_tac >> irule run_inst_seq_mem_ok_of_prefix_safe >>
     fs[EVERY_MEM] >>
     drule (GEN_ALL calldata_indexed_address_prefix_safe) >>
     disch_then (qspec_then `u` mp_tac) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts st c1) s` by
    metis_tac[emit_mload_mem_ok] >>
  `run_inst_seq_mem_ok (emitted_insts st end_st) s` by
    metis_tac[run_inst_seq_mem_ok_append] >>
  asm_simp_tac bool_ss [EVERY_APPEND, EVERY_DEF, mk_inst_def, is_terminator_def] >>
  simp[is_terminator_def] >> conj_tac >- metis_tac[IS_PREFIX_TRANS] >> fs[EVERY_MEM]
QED
Finalise abi_decode_array_head_memory

Theorem abi_decode_array_head_setup_path_mem:
  abi_decode_array_head_setup ip src asz st = ((idx,data,head),st') /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  w2n p + 32 <= s.vs_alloca_next /\
  eval_operand src s = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand idx t = SOME (n2w j) /\
    eval_operand data t = SOME (n2w (sb+32)) /\
    eval_operand head t = SOME (n2w (sb+32+j*asz)) /\
    abi_decoder_operand_live st'.cs_next_var idx /\
    abi_decoder_operand_live st'.cs_next_var data /\
    abi_decoder_operand_live st'.cs_next_var head /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t
Proof
  strip_tac >> drule_all calldata_head_setup_repeat >> strip_tac >>
  drule_all abi_decode_array_head_memory >> strip_tac >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions)`
    by simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st') /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st')) = 0`
    by (fs[EVERY_MEM, FILTER_EQ_NIL] >> metis_tac[]) >>
  drule_all run_inst_seq_gas_path_mem >> disch_then (qspec_then `ctx` assume_tac) >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts`
    by gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  qexists_tac `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> gvs[]
QED

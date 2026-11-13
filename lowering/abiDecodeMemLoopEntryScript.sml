(* The actual prefix transfer into a memory decoder's array loop. *)
Theory abiDecodeMemLoopEntry
Ancestors
  abiDecoderRecursiveLoopEntry abiDecoderLoopRegisters
  stmtForRangeMemoryParts abiDecoderContract memSafeRun
  fragGasPathMem fragExec emitHelperProps exprLoweringProps localPtrsProps
  allocaHistory instMemFrontier venomExecSemantics venomInstProofs venomInst
  venomState list rich_list words

Theorem abi_decode_mem_loop_prefix_path:
  abi_decode_loop_prefix ip src MLOAD base_op start = (labels,st) /\
  abi_decode_array_element_setup ip src dst MLOAD base_op hi di asz msz st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) MLOAD base_op hi di middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),final) /\
  fn_has_code start final func /\
  s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\ ~s.vs_halted ==>
  let t = jump_to (FST labels) s in
    gas_path_mem ctx func s 0 (OK t) /\
    t.vs_current_bb = FST labels /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    t.vs_memory = s.vs_memory /\ t.vs_vars = s.vs_vars /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    (!op. eval_operand op t = eval_operand op s) /\
    (alloca_inv s /\ alloca_room ctx func s /\ alloca_history func s ==>
      alloca_inv t /\ alloca_room ctx func t /\ alloca_history func t)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abiDecoderRecursiveLoopEntryTheory.abi_decoder_loop_phase_entry >> strip_tac >>
  conj_tac
  >- (irule for_range_jump_at_zero_path_mem >> simp[] >>
      qexists_tac `mk_inst start.cs_next_id JMP [Label (FST labels)] []` >>
      simp[get_instruction_def, EL_APPEND_EQN, mk_inst_def, is_terminator_def,
           below_frontier_no_ranges, inst_dload_in_section_def, step_inst_base_opcode_eqs]) >>
  simp[jump_to_def] >> strip_tac >>
  conj_tac >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
  conj_tac >- (irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  irule alloca_history_jump >> simp[] >> qexists_tac `s` >> simp[]
QED

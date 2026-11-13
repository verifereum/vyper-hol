(* Memory safety of the ABI builtin's length load and pure guards. *)
Theory abiDecodeMemHeader
Ancestors
  abiBuiltinDecodeHeader abiBuiltinDecodeSetup abiBuiltinPrefix
  abiBuiltinLengthGuard abiBuiltinBoundTests abiBuiltinAllocation abiDecoderContract
  abiBuiltinSetupReach entryDecoderHistoryFrame entrySinkExtraction context
  abiDecoderLoop loweringStateRelDefs
  fragGasSeqMem fragGasPathMem allocaHistoryFragment
  fragExecMem freshWrites instMemFrontier bodyUnopFragMemory memSafeRun
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words list rich_list arithmetic

Theorem abi_decode_header_memory_shape[local]:
  abi_builtin_decode_header data min_size max_size st = (inputs,last) ==>
  ?tail. emitted_insts st last =
    mk_inst st.cs_next_id MLOAD [data]
      [STRING #"%" (toString st.cs_next_var)] :: tail /\
    EVERY (\i. fresh_write_op i.inst_opcode) tail
Proof
  Cases_on `min_size = max_size` >>
  simp[abi_builtin_decode_header_def, abi_builtin_length_guard_def,
    abi_builtin_interval_guard_def, abi_builtin_eq_guard_def,
    abi_builtin_bound_test_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, fresh_write_op_def]
QED

Theorem abi_decode_header_mem_ok:
  abi_builtin_decode_header data min_size max_size st = (inputs,last) /\
  eval_operand data s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st last) s
Proof
  strip_tac >> drule abi_decode_header_memory_shape >> strip_tac >>
  asm_rewrite_tac[] >> simp_tac bool_ss [run_inst_seq_mem_ok_def] >>
  conj_tac
  >- simp[mk_inst_def, below_frontier_MLOAD, inst_dload_in_section_def] >>
  Cases_on `step_inst_base
    (mk_inst st.cs_next_id MLOAD [data]
      [STRING #"%" (toString st.cs_next_var)]) s` >> simp[] >>
  irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >>
  rpt strip_tac >> first_x_assum drule >>
  rw[fresh_write_op_def] >>
  simp[below_frontier_no_ranges, inst_dload_in_section_other]
QED

Theorem abi_decode_setup_mem_ok:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  eval_operand data s = SOME p /\ w2n p + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st ready) s
Proof
  strip_tac >> drule abi_builtin_decode_setup_trace >> strip_tac >>
  drule abi_builtin_decode_header_shape >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `emitted_insts st ready = emitted_insts st header_st ++
     emitted_insts header_st ready` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st header_st) s` by
    (irule abi_decode_header_mem_ok >> metis_tac[]) >>
  asm_rewrite_tac[] >> MATCH_MP_TAC run_inst_seq_mem_ok_append >>
  asm_rewrite_tac[] >>
  rpt strip_tac >>
  simp[run_inst_seq_mem_ok_last, mk_inst_def,
       below_frontier_no_ranges, inst_dload_in_section_other]
QED

Theorem abi_decode_setup_no_gas[local]:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) ==>
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts st ready) = []
Proof
  Cases_on `min_size = max_size` >>
  simp[abi_builtin_decode_setup_def, abi_builtin_decode_header_def,
    abi_builtin_length_guard_def, abi_builtin_interval_guard_def,
    abi_builtin_eq_guard_def, abi_builtin_bound_test_def,
    compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_decode_setup_path_mem:
  abi_builtin_decode_setup data min_size max_size outsz st = (ops,ready) /\
  fn_has_code st ready func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  eval_operand data s = SOME p /\ mload (w2n p) s = n2w cnt /\
  w2n p + 32 <= s.vs_alloca_next /\
  min_size <= cnt /\ cnt <= max_size /\ max_size < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var data /\
  ((FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = NONE /\
      d = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas (abi_builtin_decode_output_site st min_size max_size) = SOME (d,outsz)) /\
  outsz < dimword (:256) /\ ready.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand (FST ops) t = SOME (n2w d) /\
    eval_operand (FST (SND ops)) t = SOME (p + 32w) /\
    eval_operand (SND (SND ops)) t = SOME (n2w cnt) /\
    fresh_vars_wrt limit_st t /\ alloca_history func t /\
    abi_builtin_allocation_frame st.cs_next_var
      (abi_builtin_decode_output_site st min_size max_size) outsz s t /\
    t.vs_current_bb = ready.cs_current_bb /\
    t.vs_inst_idx = LENGTH ready.cs_current_insts /\ ~t.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_decode_setup_execute >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st ready) s = OK u` >>
  drule abi_builtin_decode_setup_shape >> strip_tac >>
  drule_all abi_decode_setup_mem_ok >> strip_tac >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st ready) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st ready)` by
    fs[EVERY_MEM] >>
  drule_all entry_straight_line_alloca_history >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `s.vs_inst_idx + LENGTH (emitted_insts st ready) = LENGTH ready.cs_current_insts` by
    (gvs[IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND]) >>
  drule abi_decode_setup_no_gas >> strip_tac >>
  qexists_tac `u with vs_inst_idx := LENGTH ready.cs_current_insts` >>
  gvs[eval_operand_inst_idx, fresh_vars_wrt_def, abi_builtin_allocation_frame_def]
QED

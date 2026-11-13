(* Counted memory-safe execution of the calldata array element setup. *)
Theory sourceArraySetupGasMem
Ancestors
  calldataDynStep fragGasSeqMem fragExecMem abiDecoderContract abiDecoderArraySetupInputs abiEncoder
  stmtReasonLitFragMemory abiDecoderTypedCompose
  abiDecoderLoopSetup abiDecoderDynamicLoopSetup abiDecoderIndexedAddress abiDecoderRange
  abiDecoderGuards compileEnv emitHelper emitHelperProps exprLoweringProps
  venomInst venomState venomExecSemantics words list rich_list arithmetic

Theorem source_array_setup_no_gas[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    di abi_sz mem_sz st = (ops,st') ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts st st')
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  Cases_on `dec_info_needs_offset di` >>
  asm_simp_tac bool_ss [abi_decode_array_element_setup_def,
    abi_decode_indexed_address_def, compile_abi_decode_dyn_elem_ptr_def,
    compile_abi_dec_addr_def, compile_abi_decode_range_check_def,
    comp_bind_def, comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[emitted_insts_def, mk_inst_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp_tac bool_ss [DROP_LENGTH_APPEND, APPEND] >> simp[mk_inst_def]
QED

Theorem source_array_setup_gas_path_mem:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) (Lit 0w)
    di abi_sz mem_sz st = (ops,st') /\
  eval_operand ip initial = SOME p /\
  w2n p + 32 <= initial.vs_alloca_next /\
  fn_has_code st st' fn /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq (emitted_insts st st') initial = OK last ==>
  gas_path_mem ctx fn initial 0
    (OK (last with vs_inst_idx := LENGTH st'.cs_current_insts))
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  `inst_extends st st'` by metis_tac[abi_decoder_inst_extends_prefix] >>
  drule calldata_element_setup_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st st') initial` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >>
     reverse conj_tac >- gvs[EVERY_MEM] >>
     ho_match_mp_tac (GEN_ALL calldata_element_setup_prefix_safe) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts st st')` by
    metis_tac[source_array_setup_no_gas] >>
  `st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    gvs[inst_extends_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts st st') = []` by
    simp[FILTER_EQ_NIL] >>
  `lookup_block initial.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts st st') (DROP initial.vs_inst_idx bb.bb_instructions)` by
    simp[] >>
  drule_all run_inst_seq_gas_path_mem >>
  simp[]
QED

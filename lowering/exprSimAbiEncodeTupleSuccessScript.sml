Theory exprSimAbiEncodeTupleSuccess
Ancestors
  exprSimAbiEncodeTupleExecution exprSimAbiEncodeExecFrame
  exprSimHash abiTupleEncodePrepare abiTupleEncodeSlot
  context compileEnv abiTupleProps emitHelper emitHelperProps exprLoweringProps exprLowering
  fragExec venomInst list rich_list arithmetic intCallCallee
  stmtSimLogExecFields exprSimAbiEncodeSemantic exprSimAbiEncodeMemoryLength

Theorem abi_encode_tuple_slot_opcodes:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) ==>
  EVERY (\i. MEM i.inst_opcode [ADD; MSTORE; MCOPY]) (emitted_insts st final)
Proof
  Cases_on `is_word_type ty` >> Cases_on `type_memory_bytes ce ty` >>
  asm_simp_tac (srw_ss()) [compile_abi_tuple_slot_def, compile_copy_memory_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem abi_encode_tuple_store_opcodes:
  !xs ce buf off st final.
  compile_store_abi_tuple ce buf off xs st = ((),final) ==>
  EVERY (\i. MEM i.inst_opcode [ADD; MSTORE; MCOPY]) (emitted_insts st final)
Proof
  Induct >- simp[compile_store_abi_tuple_def, comp_return_def, emitted_insts_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = ((),middle)` >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `emitted_insts st final = emitted_insts st middle ++ emitted_insts middle final` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  asm_rewrite_tac [EVERY_APPEND] >> conj_tac
  >- (drule abi_encode_tuple_slot_opcodes >> simp[]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem abi_encode_tuple_stage_opcodes:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) ==>
  EVERY (\i. MEM i.inst_opcode [ALLOCA; ADD; MSTORE; MCOPY]) (emitted_insts st staged)
Proof
  strip_tac >>
  drule abi_tuple_encode_alloc_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `emitted_insts st staged = emitted_insts st allocated ++ emitted_insts allocated staged` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  asm_rewrite_tac [EVERY_APPEND] >> conj_tac
  >- (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
      simp[contextTheory.compile_alloc_buffer_def, emit_op_def,
        comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
      strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def]) >>
  drule abi_encode_tuple_store_opcodes >>
  simp[EVERY_MEM] >> metis_tac[]
QED

Theorem abi_encode_tuple_staging_path:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st staged func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq (emitted_insts st staged) s = OK actual ==>
  gas_marked_path F ctx func s 0
    (OK (actual with vs_inst_idx := LENGTH staged.cs_current_insts)) /\
  ~actual.vs_halted /\ actual.vs_current_bb = staged.cs_current_bb
Proof
  strip_tac >> drule_all abi_tuple_encode_stage_shape >> strip_tac >>
  drule_all abi_encode_tuple_stage_opcodes >> strip_tac >>
  `staged.cs_current_insts = st.cs_current_insts ++ emitted_insts st staged` by
    fs[inst_extends_def] >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st staged)) = 0` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> simp[]) >>
  drule_all hash_run_path >> disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

Theorem abi_encode_tuple_staging_external:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  run_inst_seq (emitted_insts st staged) s = OK actual ==>
  log_encode_external actual = log_encode_external s
Proof
  strip_tac >> drule_all abi_encode_tuple_stage_opcodes >> strip_tac >>
  irule log_encode_run_external >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM, log_encode_safe_opcode_def] >> metis_tac[]
QED

Theorem abi_encode_tuple_staging_exec_frame:
  compile_alloc_buffer n st = (buf,allocated) /\
  compile_store_abi_tuple ce buf.buf_operand 0 xs allocated = ((),staged) /\
  fn_has_code st staged func /\
  run_inst_seq (emitted_insts st staged) s = OK actual ==>
  abi_encode_exec_frame func s actual
Proof
  strip_tac >> drule_all abi_encode_tuple_stage_opcodes >> strip_tac >>
  drule_all abi_encode_tuple_staging_external >>
  disch_then (strip_assume_tac o MATCH_MP log_encode_external_fields) >>
  simp[abi_encode_exec_frame_def, abi_encode_semantic_obs_fields] >> conj_tac
  >- (irule run_inst_seq_static_charge >>
      goal_assum (drule_at Any) >> simp[EVERY_MEM] >> gen_tac >> disch_tac >>
      conj_tac >- (irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >> simp[]) >>
      fs[EVERY_MEM] >> first_x_assum drule >> strip_tac >> simp[]) >>
  irule abi_encode_leaf_sequence_memory_length >> goal_assum (drule_at Any) >>
  fs[EVERY_MEM] >> metis_tac[]
QED

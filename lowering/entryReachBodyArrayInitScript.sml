(* Successful array initialization and its independent observable-field frame. *)
Theory entryReachBodyArrayInit
Ancestors
  calldataDynOwned ctorAbiActualAlloc abiDecoderArrayInitExec
  venomExecProofs venomExecSemantics venomState venomInst
  abiDecoderArrayLoopInit abiDecoderDynarrayPrefix abiDecoderArrayHeader
  abiDecoderIndexInit abiDecoderGuards abiDecoderContract
  emitHelperProps exprLoweringProps finite_map words list rich_list
  abiDecoderDynarrayBound abiEncoder emitHelper compileEnv context

Theorem entry_init_step_fields[local]:
  MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; MSTORE; ALLOCA] /\
  step_inst_base i s = OK t ==>
  (t.vs_accounts, t.vs_transient, t.vs_logs, t.vs_tx_ctx,
   t.vs_block_ctx, t.vs_outcomes, t.vs_requests, t.vs_pending_deletions,
   t.vs_gas_readings, t.vs_fmp, t.vs_halted) =
  (s.vs_accounts, s.vs_transient, s.vs_logs, s.vs_tx_ctx,
   s.vs_block_ctx, s.vs_outcomes, s.vs_requests, s.vs_pending_deletions,
   s.vs_gas_readings, s.vs_fmp, s.vs_halted)
Proof
  simp_tac bool_ss [MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  asm_simp_tac bool_ss [exec_read1_def, exec_pure1_def,
       exec_pure2_def, exec_write2_def, exec_alloca_def] >>
  simp[AllCaseEqs()] >> strip_tac >>
  gvs[update_var_def, mstore_def, write_memory_with_expansion_def,
      write_memory_def, expand_memory_def]
QED

Theorem entry_init_sequence_fields[local]:
  !code s t.
  EVERY (\i. MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; MSTORE; ALLOCA]) code /\
  run_inst_seq code s = OK t ==>
  (t.vs_accounts, t.vs_transient, t.vs_logs, t.vs_tx_ctx,
   t.vs_block_ctx, t.vs_outcomes, t.vs_requests, t.vs_pending_deletions,
   t.vs_gas_readings, t.vs_fmp, t.vs_halted) =
  (s.vs_accounts, s.vs_transient, s.vs_logs, s.vs_tx_ctx,
   s.vs_block_ctx, s.vs_outcomes, s.vs_requests, s.vs_pending_deletions,
   s.vs_gas_readings, s.vs_fmp, s.vs_halted)
Proof
  Induct >- simp[run_inst_seq_def] >> rpt gen_tac >>
  simp_tac (srw_ss()) [run_inst_seq_def, EVERY_DEF, AllCaseEqs(), Excl "MEM"] >> strip_tac >>
  `MEM h.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; MSTORE; ALLOCA]` by simp[] >>
  drule_all entry_init_step_fields >> strip_tac >>
  rename1 `run_inst_seq code middle = OK t` >>
  first_x_assum (qspecl_then [`middle`, `t`] mp_tac) >> gvs[MEM]
QED

Theorem entry_array_init_opcodes[local]:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    (setup,loop_st) ==>
  EVERY (\i. MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; MSTORE; ALLOCA])
    (emitted_insts st loop_st)
Proof
  simp[abi_decode_array_loop_init_def, abi_decode_dynarray_prefix_def,
       abi_decode_count_guard_def, abi_decode_dynarray_end_guard_def,
       abi_decode_array_header_def, abi_decode_index_init_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem entry_array_init_sequence_fields:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    (setup,loop_st) /\
  run_inst_seq (emitted_insts st loop_st) s = OK t ==>
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_requests = s.vs_requests /\
  t.vs_pending_deletions = s.vs_pending_deletions /\
  t.vs_gas_readings = s.vs_gas_readings /\ t.vs_fmp = s.vs_fmp /\
  t.vs_halted = s.vs_halted
Proof
  strip_tac >> drule entry_array_init_opcodes >> strip_tac >>
  drule_all entry_init_sequence_fields >> simp[]
QED

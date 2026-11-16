(* Operational framing of the given successful finite bulk decoder run. *)
Theory calldataBulkOperationalCertificate
Ancestors
  calldataBulkLive calldataFiniteTransport calldataBulkLeaf abiDecoderBulk
  abiDecoderReservation abiDecoderContract abiEncoder
  entryReachBodyExactArrayLoop ctorAbiActualAlloc
  safeSequence fragExecMem emitHelper exprLoweringProps compileEnv loweringStateRelDefs
  venomExecSemantics venomState venomInst finite_map pred_set words list rich_list arithmetic

Theorem bulk_step_fields[local]:
  MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; MSTORE; MUL; ADD; CALLDATACOPY] /\
  step_inst_base i s = OK t ==> entry_loop_fields s t
Proof
  simp_tac bool_ss [MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_rewrite_tac[step_inst_base_def] >>
  pure_asm_rewrite_tac[opcode_case_def] >>
  simp[exec_read1_def, exec_write2_def, exec_pure2_def, exec_pure1_def, AllCaseEqs()] >> strip_tac >>
  gvs[entry_loop_fields_def, update_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem bulk_code_shape[local]:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),last) /\
  ~dec_info_needs_clamp ei /\ last.cs_next_var <= limit.cs_next_var ==>
  EVERY (\i. MEM i.inst_opcode
    [CALLDATALOAD; GT; ISZERO; ASSERT; MSTORE; MUL; ADD; CALLDATACOPY] /\
    EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < limit.cs_next_var)
      i.inst_outputs) (emitted_insts st last)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def,
    compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem bulk_sequence_fields[local]:
  !code s t. run_inst_seq code s = OK t /\
    EVERY (\i. MEM i.inst_opcode
      [CALLDATALOAD; GT; ISZERO; ASSERT; MSTORE; MUL; ADD; CALLDATACOPY]) code ==>
    entry_loop_fields s t
Proof
  Induct >- simp[run_inst_seq_def, entry_loop_fields_def] >>
  rpt gen_tac >>
  simp_tac bool_ss [run_inst_seq_def, EVERY_DEF, AllCaseEqs(),
    exec_result_distinct, GSYM exec_result_distinct, exec_result_11] >>
  strip_tac >>
  `entry_loop_fields s ss'` by
    (irule bulk_step_fields >> qexists `h` >> asm_rewrite_tac[]) >>
  first_x_assum drule_all >> gvs[entry_loop_fields_def]
QED

Theorem bulk_sequence_fresh[local]:
  run_inst_seq code s = OK t /\ fresh_vars_wrt limit s /\
  EVERY (\i. ~is_terminator i.inst_opcode /\
    EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < limit.cs_next_var)
      i.inst_outputs) code ==>
  fresh_vars_wrt limit (t with vs_inst_idx := idx)
Proof
  strip_tac >> simp[fresh_vars_wrt_def] >> rpt strip_tac >>
  `lookup_var (STRING #"%" (toString n)) t =
   lookup_var (STRING #"%" (toString n)) s` by
    (irule ctor_actual_sequence_var_frame >> qexists `code` >> simp[] >>
     gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     first_x_assum drule >> simp[] >> decide_tac) >>
  gvs[fresh_vars_wrt_def, lookup_var_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem calldata_bulk_accepted_operational:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),last) /\
  ~dec_info_needs_clamp ei /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\
  d+(32+maxn*mem_sz) < dimword (:256) /\
  d+(32+maxn*mem_sz) <= s.vs_alloca_next /\
  fn_has_code st last fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  run_inst_seq (emitted_insts st last) s = OK t /\
  last.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s ==>
  ~(t with vs_inst_idx := LENGTH last.cs_current_insts).vs_halted /\
  (t with vs_inst_idx := LENGTH last.cs_current_insts).vs_current_bb = last.cs_current_bb /\
  (t with vs_inst_idx := LENGTH last.cs_current_insts).vs_inst_idx = LENGTH last.cs_current_insts /\
  fresh_vars_wrt limit (t with vs_inst_idx := LENGTH last.cs_current_insts) /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_logs = s.vs_logs /\ t.vs_outcomes = s.vs_outcomes /\
  t.vs_requests = s.vs_requests /\ t.vs_pending_deletions = s.vs_pending_deletions /\
  t.vs_tx_ctx = s.vs_tx_ctx /\ t.vs_block_ctx = s.vs_block_ctx /\
  t.vs_fmp = s.vs_fmp /\ t.vs_gas_readings = s.vs_gas_readings /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!fuel r. run_from fuel ctx fn (t with vs_inst_idx := LENGTH last.cs_current_insts) = r /\
      (!err. r <> Error err) ==>
    ?fuel'. run_from fuel' ctx fn s = r /\
      (mem_safe_run fuel ctx fn (t with vs_inst_idx := LENGTH last.cs_current_insts) ==>
       mem_safe_run fuel' ctx fn s))
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all calldata_bulk_opcodes >> strip_tac >>
  drule_all bulk_code_shape >> strip_tac >>
  `frag_exec_mem ctx st last (\u. u = s)
    (\u. u = t with vs_inst_idx := LENGTH last.cs_current_insts) (K F)` by
    (irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     ho_match_mp_tac (GEN_ALL calldata_bulk_live_prefix_safe) >>
     qexistsl [`src`,`p`,`mem_sz`,`maxn`,`ei`,`dst`,`d`,`abi_sz`] >> simp[]) >>
  `entry_loop_fields s t` by
    (irule bulk_sequence_fields >> qexists `emitted_insts st last` >>
     simp[] >> gvs[EVERY_MEM] >> metis_tac[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >>
     qexists `emitted_insts st last` >> simp[] >>
     irule listTheory.EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
     simp[] >> rpt strip_tac >> gvs[is_terminator_def, is_alloca_op_def]) >>
  `fresh_vars_wrt limit (t with vs_inst_idx := LENGTH last.cs_current_insts)` by
    (irule bulk_sequence_fresh >> qexistsl [`emitted_insts st last`,`s`] >>
     simp[] >> irule listTheory.EVERY_MONOTONIC >> goal_assum (drule_at Any) >>
     simp[] >> rpt strip_tac >> gvs[is_terminator_def]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [frag_exec_mem_def] >>
  disch_then (qspec_then `fn` mp_tac) >>
  simp[entry_loop_fields_def] >> strip_tac >> gvs[entry_loop_fields_def]
QED

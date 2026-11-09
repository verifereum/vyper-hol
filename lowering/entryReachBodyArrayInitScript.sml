(* Successful array initialization and its independent observable-field frame. *)
Theory entryReachBodyArrayInit
Ancestors
  valueEncodingDefs calldataDynOwned ctorAbiActualAlloc abiDecoderArrayInitExec
  venomExecProofs venomExecSemantics venomState venomInst
  abiDecoderArrayLoopInit abiDecoderDynarrayPrefix abiDecoderArrayHeader
  abiDecoderIndexInit abiDecoderGuards abiDecoderContract
  emitHelperProps exprLoweringProps finite_map words list rich_list
  abiDecoderDynarrayBound abiEncoder emitHelper compileEnv context abiDecoderReentry
  allocaFrontierBound allocaBudgetProps venomMemDefs abiDecoderFrameCompose

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
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    (setup,loop_st) ==>
  EVERY (\i. MEM i.inst_opcode [CALLDATALOAD; GT; ISZERO; ASSERT; MSTORE; ALLOCA])
    (emitted_insts st loop_st)
Proof
  simp[abi_decode_array_loop_init_def, abi_decode_dynarray_prefix_def,
       abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_position_prefix_unbounded,
       compile_abi_dec_addr_def,
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
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
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

Theorem entry_array_prepare_accepted[local]:
  abi_decode_count_guard CALLDATALOAD src maxn st = (cop,guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_load CALLDATALOAD srcword s = n2w ncount /\ ncount <= maxn ==>
  ?h. run_inst_seq (emitted_insts st header_st) s = OK h /\
    eval_operand cnt h = SOME (n2w ncount) /\
    mem_word_at d h.vs_memory = n2w ncount /\
    abi_decode_frame d 32 s h /\
    h.vs_allocas = s.vs_allocas /\ h.vs_alloca_next = s.vs_alloca_next /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op h = eval_operand op s) /\
    h.vs_halted = s.vs_halted
Proof
  strip_tac >>
  `w2n (abi_decode_load CALLDATALOAD srcword s) <= maxn` by simp[] >>
  drule_all calldata_count_guard_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st guard_st) s = OK g` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  `st.cs_next_var <= guard_st.cs_next_var` by
    (qpat_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
          fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  `eval_operand src g = SOME srcword /\ eval_operand dst g = SOME (n2w d)` by metis_tac[] >>
  `abi_decoder_operand_live guard_st.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all calldata_array_header_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts guard_st header_st) g = OK h` >>
  `run_inst_seq (emitted_insts st header_st) s = OK h` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`g`, `guard_st`] >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op h = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live guard_st.cs_next_var op` by
       (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
     metis_tac[]) >>
  qexists_tac `h` >> gvs[abi_decode_load_def, abi_decode_source_def, abi_decode_frame_def] >>
  first_assum ACCEPT_TAC
QED

Theorem entry_index_accepted[local]:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  alloca_frontier_inv ctx fn site s /\
  unit_alloca_budget ctx < dimword (:256) /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
   (FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= s.vs_alloca_next)) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (if FLOOKUP s.vs_allocas st.cs_next_id = NONE then
       t.vs_alloca_next = s.vs_alloca_next+32
     else t.vs_alloca_next = s.vs_alloca_next)
Proof
  strip_tac
  >- (drule_all calldataDynInitTheory.calldata_index_init_fresh_sequence >>
      strip_tac >> qexists_tac `t` >> gvs[]) >>
  drule_all calldataDynInitTheory.calldata_index_init_reuse_sequence >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED

Theorem entry_index_sequence_frame[local]:
  abi_decode_index_init st = (ip,st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  eval_operand ip t = SOME (n2w p) /\ p < dimword (:256) ==>
  abi_decode_frame p 32 s t
Proof
  strip_tac >> drule calldataDynInitTheory.calldata_index_init_instructions >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  rename1 `step_inst_base (mk_inst st.cs_next_id ALLOCA _ _) s = OK a` >>
  `?q. eval_operand ip a = SOME (n2w q) /\ q < dimword (:256)` by
    (qpat_x_assum `step_inst_base _ s = _` mp_tac >>
     simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
     strip_tac >> gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     metis_tac[arithmeticTheory.MOD_MOD, arithmeticTheory.MOD_LESS,
               wordsTheory.ZERO_LT_dimword]) >>
  drule_all calldataDynInitTheory.calldata_index_init_after_alloca >> strip_tac >>
  `t = mstore q 0w a` by gvs[run_inst_seq_def, AllCaseEqs()] >>
  `p = q` by gvs[n2w_11] >>
  gvs[] >> irule calldata_index_init_repeat_memory_frame >>
  goal_assum (drule_at Any)
QED

Theorem entry_header_count_live[local]:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') ==>
  abi_decoder_operand_live st'.cs_next_var cnt
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >> decide_tac
QED

Theorem entry_array_init_accepted_live:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\ unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) /\ alloca_inv initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  abi_decode_load CALLDATALOAD srcword initial = n2w ncount /\ ncount <= maxn ==>
  ?t. run_inst_seq (emitted_insts st loop_st) initial = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    eval_operand cnt t = SOME (n2w ncount) /\ mem_word_at d t.vs_memory = n2w ncount /\
    FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
       t.vs_alloca_next = initial.vs_alloca_next+32 else t.vs_alloca_next = initial.vs_alloca_next) /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    abi_decode_footprint_frame [(d,32);(p,32)] initial t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op initial) /\
    t.vs_halted = initial.vs_halted /\
    t.vs_accounts = initial.vs_accounts /\ t.vs_transient = initial.vs_transient /\
    t.vs_logs = initial.vs_logs /\ t.vs_tx_ctx = initial.vs_tx_ctx /\
    t.vs_block_ctx = initial.vs_block_ctx /\ t.vs_outcomes = initial.vs_outcomes /\
    t.vs_requests = initial.vs_requests /\ t.vs_pending_deletions = initial.vs_pending_deletions /\
    t.vs_gas_readings = initial.vs_gas_readings /\ t.vs_fmp = initial.vs_fmp
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `?cop. abi_decode_count_guard CALLDATALOAD src maxn st = (cop,guard_st)` by
    (qpat_x_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_dynarray_prefix_def, abi_decode_dynarray_end_guard_def,
          comp_bind_def, comp_return_def] >> pairarg_tac >> simp[] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all entry_array_prepare_accepted >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st header_st) initial = OK h` >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `alloca_frontier_inv ctx fn site h /\ alloca_inv h` by
    (gvs[alloca_frontier_inv_def, remaining_alloca_budget_def, alloca_inv_def,
         allocas_non_overlapping_def, alloca_next_valid_def] >> metis_tac[]) >>
  `?t. run_inst_seq (emitted_insts header_st loop_st) h = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP h.vs_allocas id) /\
    (if FLOOKUP h.vs_allocas header_st.cs_next_id = NONE then
       t.vs_alloca_next = h.vs_alloca_next+32 else t.vs_alloca_next = h.vs_alloca_next)` by
    (irule entry_index_accepted >> goal_assum (drule_at Any) >>
     gvs[] >> qexistsl_tac [`ctx`, `fn`, `site`] >> simp[]) >>
  `alloca_inv t /\ alloca_frontier_inv ctx fn site t` by
    (qsuff_tac `alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
       h.vs_alloca_next <= t.vs_alloca_next /\
       (!id b cap. FLOOKUP h.vs_allocas id = SOME (b,cap) ==>
          FLOOKUP t.vs_allocas id = SOME (b,cap))` >- simp[] >>
     irule calldata_index_init_owned_fields >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl_tac [`ip`, `p`, `header_st`, `loop_st`] >> gvs[]) >>
  `run_inst_seq (emitted_insts st loop_st) initial = OK t` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`h`, `header_st`] >> simp[] >>
     metis_tac[inst_extends_trans]) >>
  drule_all entry_array_init_sequence_fields >> strip_tac >>
  drule_all ctor_actual_index_var_frame >> strip_tac >>
  `p < dimword (:256)` by suspend "pointer" >>
  `abi_decode_frame p 32 h t` by
    (drule_all entry_index_sequence_frame >> simp[]) >>
  drule_all entry_header_count_live >> strip_tac >>
  `eval_operand cnt t = SOME (n2w ncount)` by metis_tac[] >>
  `mem_word_at d t.vs_memory = n2w ncount` by suspend "header" >>
  `abi_decode_footprint_frame [(d,32);(p,32)] initial t` by
    (irule abi_decoder_array_init_exact_frame >> qexists_tac `h` >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op initial` by
    (rpt strip_tac >> `abi_decoder_operand_live header_st.cs_next_var op` by
      (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[]
QED

Resume entry_array_init_accepted_live[pointer]:
  `initial.vs_alloca_next < dimword (:256)` by
    (qpat_assum `alloca_frontier_inv ctx fn site initial` mp_tac >>
     simp_tac bool_ss [alloca_frontier_inv_def] >> strip_tac >> decide_tac) >>
  qpat_x_assum `(_ /\ p = _) \/ _` strip_assume_tac >> gvs[]
QED

Resume entry_array_init_accepted_live[header]:
  `mem_word_at d t.vs_memory = mem_word_at d h.vs_memory` by
    (irule abi_decode_frame_mem_word >> goal_assum (drule_at Any) >> decide_tac) >> simp[]
QED

Finalise entry_array_init_accepted_live

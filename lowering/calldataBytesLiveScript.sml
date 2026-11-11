(* Reentrant count guards and zero-filled calldata copies. *)
Theory calldataBytesLive
Ancestors
  abiDecoderRange
  calldataWordLive calldataWordLeaf calldataBytesLeaf calldataDynOwned abiDecoderReentry
  abiDecoderBytes abiDecoderCopy abiDecoderGuards abiEncoder
  abiDecoderContract abiDecoderComposition valueEncoding safeSequence
  abiDecoderBytesTyped fragExecMem
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic list rich_list finite_map

Theorem calldata_count_guard_rejected_live:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\ limit < dimword (:256) /\
  limit < w2n (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  qpat_x_assum `s1 = update_var _ _ _` kall_tac >>
  `step_inst_base (mk_inst c1.cs_next_id GT [count_op; Lit (n2w limit)]
    [STRING #"%" (toString c1.cs_next_var)]) s1 =
    OK (update_var (STRING #"%" (toString c1.cs_next_var)) 1w s1)` by
    (`(1w:bytes32) = bool_to_word
        (w2n (abi_decode_load CALLDATALOAD p s) > w2n (n2w limit:bytes32))` by
        simp[w2n_n2w, bool_to_word_def] >>
     pop_assum SUBST1_TAC >> irule step_GT >> simp[eval_operand_def]) >>
  drule_all calldata_zero_test_frame >> simp[] >> strip_tac >>
  rename1 `emit_void ASSERT [ok] c3 = ((),last)` >>
  qexists_tac `t` >> conj_tac
  >- (`inst_extends c1 last` by
        (imp_res_tac inst_extends_emit_op >>
         imp_res_tac inst_extends_emit_void >>
         metis_tac[inst_extends_trans]) >>
      `emitted_insts st last = emitted_insts st c1 ++ emitted_insts c1 last` by
        metis_tac[emitted_insts_append, inst_extends_def] >>
      asm_rewrite_tac[] >> metis_tac[run_inst_seq_append]) >>
  simp[] >> rpt strip_tac >>
  `st.cs_next_var <= c1.cs_next_var` by
    (qpat_assum `emit_op CALLDATALOAD _ _ = _`
       (mp_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem calldata_copy_exact_frame:
  emit_void CALLDATACOPY [dst;src;Lit (n2w sz)] st = ((),st') /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand src s = SOME p /\
  d < dimword (:256) /\ sz < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at d sz t.vs_memory =
      mem_bytes_at (w2n p) sz s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d sz s t /\
    (!op. eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `emit_void (abi_decode_copy_opcode CALLDATALOAD) [dst;src;Lit (n2w sz)] st = ((),st')` by
    simp[abi_decode_copy_opcode_def] >>
  `eval_operand (Lit (n2w sz)) s = SOME (n2w sz)` by simp[eval_operand_def] >>
  drule_all abi_decode_copy_sequence >> strip_tac >>
  drule_all abi_decode_copy_vars >> strip_tac >>
  qexists_tac `s'` >>
  gvs[w2n_n2w, abi_decode_copy_bytes_def, abi_decode_source_def, mem_bytes_at_def] >>
  `step_inst_base (mk_inst st.cs_next_id (abi_decode_copy_opcode CALLDATALOAD)
    [dst;src;Lit (n2w sz)] []) s =
    OK (write_memory_with_expansion d
      (abi_decode_copy_bytes CALLDATALOAD (w2n p) sz s) s)` by
    (`d = w2n (n2w d:bytes32) /\ sz = w2n (n2w sz:bytes32)` by
       simp[w2n_n2w] >>
     once_asm_rewrite_tac[] >> irule abi_decode_copy_step >> simp[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[run_inst_seq_def] >>
  simp[write_memory_with_expansion_def, eval_operand_def, lookup_var_def]
QED

Theorem calldata_bytes_accepted_live:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) /\
  maxn < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s) <= maxn ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    mem_bytes_at d (abi_decode_bytes_copy_size maxn) t.vs_memory =
      mem_bytes_at (w2n p) (abi_decode_bytes_copy_size maxn) s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (abi_decode_bytes_copy_size maxn) s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_sentinel, compile_abi_dec_addr_zero, pairTheory.UNCURRY_DEF, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[abi_decode_copy_opcode_def] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (count_op,c1)` >>
  drule_all calldata_count_guard_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p /\ eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `d < dimword (:256) /\ abi_decode_bytes_copy_size maxn < dimword (:256)` by decide_tac >>
  drule_all calldata_copy_exact_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `32 <= abi_decode_bytes_copy_size maxn` by simp[abi_decode_bytes_copy_size_def] >>
  `mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s` by
    (irule calldata_bytes_header_observation >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `t` >> gvs[abi_decode_frame_def] >> metis_tac[]
QED

Theorem calldata_bytes_rejected_live:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ maxn < dimword (:256) /\
  maxn < w2n (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_sentinel, compile_abi_dec_addr_zero, pairTheory.UNCURRY_DEF, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all calldata_count_guard_rejected_live >> strip_tac >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  qexists_tac `t` >> simp[] >> irule run_inst_seq_abort_extends >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem calldata_bytes_prefix_live:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) /\
  d + abi_decode_bytes_copy_size maxn <= s.vs_alloca_next /\
  maxn < dimword (:256) ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_sentinel, compile_abi_dec_addr_zero, pairTheory.UNCURRY_DEF, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (count_op,c1)` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac calldata_prefix_safe_append >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_count_guard_instruction_safe >> simp[]) >>
  gen_tac >> strip_tac >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD p s) <= maxn`
  >- (drule_all calldata_count_guard_repeat_sequence >> strip_tac >> gvs[] >>
      drule emitted_insts_emit_void >> simp[abi_decode_copy_opcode_def] >> strip_tac >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_copy_prefix_safe) >>
      qexists_tac `d` >> simp[] >>
      `d < dimword (:256) /\ abi_decode_bytes_copy_size maxn < dimword (:256)` by decide_tac >>
      metis_tac[]) >>
  `maxn < w2n (abi_decode_load CALLDATALOAD p s)` by decide_tac >>
  drule_all calldata_count_guard_rejected_live >> gvs[]
QED

Theorem calldata_bytes_live_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) /\
  d + abi_decode_bytes_copy_size maxn <= initial.vs_alloca_next /\
  maxn < dimword (:256) ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= maxn /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      mem_bytes_at d (abi_decode_bytes_copy_size maxn) t.vs_memory =
        mem_bytes_at (w2n p) (abi_decode_bytes_copy_size maxn) initial.vs_call_ctx.cc_calldata /\
      abi_decode_frame d (abi_decode_bytes_copy_size maxn) initial t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (\r. ?t. r = Abort Revert_abort t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_memory = initial.vs_memory /\ t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule calldata_bytes_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bytes_prefix_live) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn`
  >- (drule_all calldata_bytes_accepted_live >> strip_tac >>
      disj1_tac >> qexists_tac `t` >>
      gvs[abi_decode_frame_def, instIdxIndepTheory.eval_op_inst_idx] >> metis_tac[]) >>
  `maxn < w2n (abi_decode_load CALLDATALOAD p initial)` by decide_tac >>
  drule_all calldata_bytes_rejected_live >> strip_tac >>
  disj2_tac >> qexists_tac `t` >>
  simp[instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem calldata_count_guard_rejected_live_mod:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\
  limit MOD dimword (:256) < w2n (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_count_guard CALLDATALOAD src (limit MOD dimword (:256)) st =
    (count_op,st')` by simp[calldata_count_guard_mod_limit] >>
  drule calldata_count_guard_rejected_live >> simp[]
QED

Theorem abi_decode_bytes_copy_size_capacity:
  !n. n <= abi_decode_bytes_copy_size n
Proof
  gen_tac >>
  qspec_then `32` mp_tac DIVISION >> (impl_tac >- decide_tac) >>
  disch_then (qspec_then `n + 31` mp_tac) >>
  strip_tac >> simp[abi_decode_bytes_copy_size_def] >> decide_tac
QED

Theorem abi_decode_bytes_extent_capacity_bound:
  !d n. d + abi_decode_bytes_copy_size n < dimword (:256) ==>
    n < dimword (:256)
Proof
  rpt strip_tac >>
  qspec_then `n` assume_tac abi_decode_bytes_copy_size_capacity >> decide_tac
QED

(* Arbitrary-calldata fixed-buffer bytestring decoding. *)
Theory calldataBytesLeaf
Ancestors
  valueEncodingDefs loweringStateRelDefs safeSequence fragExecMem abiDecoderBytesTyped
  abiCanonicalHeadSize calldataWordLeaf abiDecoderReservation abiDecoderBytes abiDecoderComposition abiDecoderCopy
  abiDecoderGuards abiDecoderAllocation abiDecoderContract abiEncoder
  emitHelperProps exprLoweringProps compileEnv emitHelper valueEncoding
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem calldata_bytes_opcodes:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) hi (DecBytestring n) st = ((),st') ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st st')
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >>
  gvs[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem calldata_bytes_accepted_sequence:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) /\
  maxn < dimword (:256) /\ fresh_vars_wrt st s /\
  w2n (abi_decode_load CALLDATALOAD p s) <= maxn ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at d (abi_decode_bytes_copy_size maxn) t.vs_memory =
      mem_bytes_at (w2n p) (abi_decode_bytes_copy_size maxn) s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (abi_decode_bytes_copy_size maxn) s t /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `abi_decode_load CALLDATALOAD p s =
     n2w (w2n (abi_decode_load CALLDATALOAD p s))` by simp[] >>
  `abi_decode_bytes_copy_size maxn < dimword (:256)` by decide_tac >>
  drule_all abi_decode_bytes_sentinel_sequence >> strip_tac >>
  qexists_tac `t` >> gvs[w2n_n2w, abi_decode_source_def]
QED

Theorem calldata_bytes_allocation_shape:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring n) st = ((),st') ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  simp[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem calldata_bytes_accepted_allocation:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) /\
  maxn < dimword (:256) /\ fresh_vars_wrt st s /\
  w2n (abi_decode_load CALLDATALOAD p s) <= maxn ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at d (abi_decode_bytes_copy_size maxn) t.vs_memory =
      mem_bytes_at (w2n p) (abi_decode_bytes_copy_size maxn) s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (abi_decode_bytes_copy_size maxn) s t /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all calldata_bytes_accepted_sequence >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule abi_decode_sequence_allocation_frame >>
  qexists_tac `emitted_insts st st'` >> simp[] >>
  drule calldata_bytes_allocation_shape >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem calldata_bytes_header_observation:
  32 <= sz /\ mem_bytes_at d sz t.vs_memory =
    mem_bytes_at (w2n p) sz s.vs_call_ctx.cc_calldata ==>
  mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s
Proof
  strip_tac >>
  `mem_bytes_at d 32 t.vs_memory =
     mem_bytes_at (w2n p) 32 s.vs_call_ctx.cc_calldata` by
    (`!q mem. TAKE 32 (mem_bytes_at q sz mem) = mem_bytes_at q 32 mem` by
       (rpt gen_tac >>
        qspecl_then [`q`, `0`, `32`, `sz`, `mem`] mp_tac mem_bytes_at_window >> simp[]) >>
     metis_tac[]) >>
  gvs[mem_word_at_def, abi_decode_load_def, abi_decode_source_def,
      mem_bytes_at_def]
QED

Theorem calldata_count_guard_rejected_sequence:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\ limit < dimword (:256) /\
  limit < w2n (abi_decode_load CALLDATALOAD p s) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[w2n_n2w, bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> simp[] >> metis_tac[]
QED

Theorem calldata_bytes_rejected_sequence:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ maxn < dimword (:256) /\
  maxn < w2n (abi_decode_load CALLDATALOAD p s) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_sentinel, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all calldata_count_guard_rejected_sequence >> strip_tac >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  `?c1. inst_extends st c1 /\ inst_extends c1 st' /\
    run_inst_seq (emitted_insts st c1) s = Abort Revert_abort t` by metis_tac[] >>
  qexists_tac `t` >> irule run_inst_seq_abort_extends >>
  qexists_tac `c1` >> simp[]
QED

Theorem calldata_copy_prefix_safe:
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  sz < dimword (:256) /\ d + sz <= s.vs_alloca_next ==>
  !pre i post u. [mk_inst id CALLDATACOPY [dst; src; Lit (n2w sz)] []] =
    pre ++ i::post /\ run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  rpt strip_tac >> Cases_on `pre` >> gvs[run_inst_seq_def] >>
  simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.sized_source_write_range_def,
       mk_inst_def, eval_operand_def, w2n_n2w] >>
  Cases_on `eval_operand src s` >> simp[]
QED

Theorem calldata_count_guard_instruction_safe:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') ==>
  EVERY (\i. !s. inst_mem_below_frontier i s) (emitted_insts st st')
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def]
QED

Theorem calldata_count_guard_allocation_shape:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem calldata_bytes_prefix_safe:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) /\
  d + abi_decode_bytes_copy_size maxn <= s.vs_alloca_next /\
  maxn < dimword (:256) /\ fresh_vars_wrt st s ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_sentinel, comp_bind_def, LET_THM] >>
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
  >- (`abi_decode_load CALLDATALOAD p s =
         n2w (w2n (abi_decode_load CALLDATALOAD p s))` by simp[] >>
      drule_all abi_decode_count_guard_sequence >> strip_tac >> gvs[] >>
      drule calldata_count_guard_allocation_shape >> strip_tac >>
      drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
      drule emitted_insts_emit_void >> simp[abi_decode_copy_opcode_def] >> strip_tac >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_copy_prefix_safe) >>
      qexists_tac `d` >> simp[] >>
      `d < dimword (:256) /\ abi_decode_bytes_copy_size maxn < dimword (:256)` by decide_tac >>
      metis_tac[]) >>
  `maxn < w2n (abi_decode_load CALLDATALOAD p s)` by decide_tac >>
  drule_all calldata_count_guard_rejected_sequence >> gvs[]
QED

Theorem calldata_bytes_accepted_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) /\
  d + abi_decode_bytes_copy_size maxn <= initial.vs_alloca_next /\
  maxn < dimword (:256) /\ fresh_vars_wrt st initial /\
  w2n (abi_decode_load CALLDATALOAD p initial) <= maxn ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= maxn /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      mem_bytes_at d (abi_decode_bytes_copy_size maxn) t.vs_memory =
        mem_bytes_at (w2n p) (abi_decode_bytes_copy_size maxn) initial.vs_call_ctx.cc_calldata /\
      abi_decode_frame d (abi_decode_bytes_copy_size maxn) initial t /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule calldata_bytes_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bytes_prefix_safe) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all calldata_bytes_accepted_allocation >> strip_tac >>
  `32 <= abi_decode_bytes_copy_size maxn` by simp[abi_decode_bytes_copy_size_def] >>
  drule_all calldata_bytes_header_observation >> strip_tac >>
  qexists_tac `t` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def,
      instIdxIndepTheory.eval_op_inst_idx] >> metis_tac[]
QED

Theorem calldata_bytes_rejected_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) /\
  d + abi_decode_bytes_copy_size maxn <= initial.vs_alloca_next /\
  maxn < dimword (:256) /\ fresh_vars_wrt st initial /\
  maxn < w2n (abi_decode_load CALLDATALOAD p initial) ==>
  frag_exec_mem ctx st st' (\s. s = initial) (K F)
    (\r. ?u. r = Abort Revert_abort u)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bytes_shape >> strip_tac >>
  drule calldata_bytes_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bytes_prefix_safe) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_all calldata_bytes_rejected_sequence >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem calldata_bytes_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecBytestring maxn) st = ((),st') /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  d + abi_decode_bytes_copy_size maxn < dimword (:256) /\
  d + abi_decode_bytes_copy_size maxn <= initial.vs_alloca_next /\
  maxn < dimword (:256) /\ fresh_vars_wrt st initial ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= maxn /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      mem_bytes_at d (abi_decode_bytes_copy_size maxn) t.vs_memory =
        mem_bytes_at (w2n p) (abi_decode_bytes_copy_size maxn) initial.vs_call_ctx.cc_calldata /\
      abi_decode_frame d (abi_decode_bytes_copy_size maxn) initial t /\
      fresh_vars_wrt st' t /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (\r. ?u. r = Abort Revert_abort u)
Proof
  strip_tac >> Cases_on `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn`
  >- (drule_all calldata_bytes_accepted_frag_mem >> strip_tac >>
      first_x_assum (qspec_then `ctx` assume_tac) >>
      irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[]) >>
  `maxn < w2n (abi_decode_load CALLDATALOAD p initial)` by decide_tac >>
  drule_all calldata_bytes_rejected_frag_mem >> strip_tac >>
  first_x_assum (qspec_then `ctx` assume_tac) >>
  irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[]
QED

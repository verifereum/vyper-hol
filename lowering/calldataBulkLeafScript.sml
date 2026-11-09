(* Bulk calldata copy retains wrapped source address arithmetic. *)
Theory calldataBulkLeaf
Ancestors
  valueEncodingDefs loweringStateRelDefs fragExecMem safeSequence calldataWordLeaf abiDecoderReservation abiDecoderDynarrayPrefix abiDecoderArrayHeader abiDecoderFrameCompose calldataBytesLeaf abiDecoderBulk abiDecoderDynarrayBound abiDecoderBytesBound abiDecoderComposition
  abiDecoderContract abiDecoderCopy abiDecoderGuards abiDecoderRange abiEncoder emitHelperProps
  exprLoweringProps compileEnv emitHelper valueEncoding venomExecSemantics
  venomState venomInst words arithmetic list rich_list

Theorem calldata_bulk_opcodes:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
    (emitted_insts st st')
Proof
  strip_tac >> Cases_on `hi = Lit 0w` >>
  gvs[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def] >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem calldata_bulk_payload_sequence:
  abi_decode_bulk_payload dst src cnt mem_sz CALLDATALOAD (Lit 0w) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand cnt s = SOME (n2w n) /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at (d + 32) (n * mem_sz) t.vs_memory =
      mem_bytes_at (w2n (p + 32w)) (n * mem_sz) s.vs_call_ctx.cc_calldata /\
    abi_decode_frame (d + 32) (n * mem_sz) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  simp[abi_decode_bulk_payload_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] st = (sz_op,c1)` >>
  rename1 `emit_op ADD [src; Lit 32w] c1 = (src_data,c2)` >>
  rename1 `emit_op ADD [dst; Lit 32w] c2 = (dst_data,c3)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz)` by simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >> gvs[word_mul_n2w] >>
  `eval_operand src s1 = SOME p` by metis_tac[] >>
  `eval_operand (Lit 32w) s1 = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand dst s2 = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit 32w) s2 = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `eval_operand sz_op s3 = SOME (n2w (n * mem_sz)) /\
   eval_operand src_data s3 = SOME (p + 32w)` by
    (ONCE_REWRITE_TAC [MULT_COMM] >> metis_tac[]) >>
  drule_all abi_decode_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 st') s3 = OK t` >>
  `fresh_vars_wrt st' t` by (drule_all abi_decode_copy_fresh >> simp[]) >>
  drule inst_extends_emit_void >> strip_tac >>
  `run_inst_seq (emitted_insts c2 st') s2 = OK t /\ inst_extends c2 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s3`, `c3`] >> simp[]) >>
  `run_inst_seq (emitted_insts c1 st') s1 = OK t /\ inst_extends c1 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  qexists_tac `t` >> gvs[word_add_n2w, w2n_n2w, abi_decode_copy_bytes_def,
    mem_bytes_at_def, abi_decode_source_def, abi_decode_frame_def] >> metis_tac[]
QED

Theorem calldata_bulk_body_sequence:
  abi_decode_bulk_body dst src src CALLDATALOAD (Lit 0w) mem_sz st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load CALLDATALOAD p s = n2w n /\
  d + 32 < dimword (:256) /\ n * mem_sz < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = n2w n /\
    mem_bytes_at (d + 32) (n * mem_sz) t.vs_memory =
      mem_bytes_at (w2n (p + 32w)) (n * mem_sz) s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (32 + n * mem_sz) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  simp_tac bool_ss [abi_decode_bulk_body_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_array_header dst src CALLDATALOAD st = (cnt,c1)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `d < dimword (:256)` by decide_tac >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p /\ eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `eval_operand cnt s1 = SOME (n2w n)` by metis_tac[] >>
  `n * mem_sz < dimword (:256)` by metis_tac[MULT_COMM] >>
  drule_all calldata_bulk_payload_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `mem_word_at d t.vs_memory = mem_word_at d s1.vs_memory` by
    (irule abi_decode_frame_mem_word >> qexistsl_tac [`d+32`, `n*mem_sz`] >> simp[]) >>
  `s1.vs_call_ctx = s.vs_call_ctx` by gvs[abi_decode_frame_def] >>
  `abi_decode_frame d (32 + n * mem_sz) s t` by
    (irule abi_decode_frame_adjacent >> qexists_tac `s1` >> simp[]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

Theorem calldata_bulk_sentinel:
  ~dec_info_needs_clamp ei ==>
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) =
  do cnt <- abi_decode_count_guard CALLDATALOAD src maxn;
     abi_decode_bulk_body dst src src CALLDATALOAD (Lit 0w) mem_sz
  od
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases] >>
  simp[abi_decode_dynarray_prefix_def, abi_decode_dynarray_end_guard_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, FUN_EQ_THM] >>
  rpt gen_tac >>
  Cases_on `abi_decode_count_guard CALLDATALOAD src maxn x` >> simp[]
QED

Theorem calldata_bulk_accepted_sequence:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME (n2w d) /\
  w2n (abi_decode_load CALLDATALOAD p s) <= maxn /\
  maxn < dimword (:256) /\ d + 32 < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s) * mem_sz < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    mem_bytes_at (d+32) (w2n (abi_decode_load CALLDATALOAD p s) * mem_sz) t.vs_memory =
      mem_bytes_at (w2n (p+32w)) (w2n (abi_decode_load CALLDATALOAD p s) * mem_sz)
        s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (32 + w2n (abi_decode_load CALLDATALOAD p s) * mem_sz) s t /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [calldata_bulk_sentinel, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (count_op,c1)` >>
  `abi_decode_load CALLDATALOAD p s = n2w (w2n (abi_decode_load CALLDATALOAD p s))` by simp[] >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p /\ eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `abi_decode_load CALLDATALOAD p s1 = n2w (w2n (abi_decode_load CALLDATALOAD p s))` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  `w2n (abi_decode_load CALLDATALOAD p s) * mem_sz < dimword (:256)` by metis_tac[MULT_COMM] >>
  drule_all calldata_bulk_body_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> gvs[abi_decode_frame_def] >> metis_tac[]
QED

Theorem calldata_bulk_allocation_shape:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              ~is_alloca_op i.inst_opcode) (emitted_insts st st')
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  simp[compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem calldata_bulk_rejected_sequence:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src s = SOME p /\
  maxn < dimword (:256) /\ maxn < w2n (abi_decode_load CALLDATALOAD p s) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [calldata_bulk_sentinel, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all calldata_count_guard_rejected_sequence >> strip_tac >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (cnt,cs')` >>
  `inst_extends cs' st'` by
    (qpat_x_assum `abi_decode_bulk_body _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_bulk_body_def, abi_decode_array_header_def,
          abi_decode_bulk_payload_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     metis_tac[inst_extends_trans]) >>
  qexists_tac `t` >> irule run_inst_seq_abort_extends >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem calldata_bulk_accepted_allocation:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME (n2w d) /\
  w2n (abi_decode_load CALLDATALOAD p s) <= maxn /\
  maxn < dimword (:256) /\ d + (32 + maxn * mem_sz) < dimword (:256) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    mem_bytes_at (d+32) (w2n (abi_decode_load CALLDATALOAD p s) * mem_sz) t.vs_memory =
      mem_bytes_at (w2n (p+32w)) (w2n (abi_decode_load CALLDATALOAD p s) * mem_sz)
        s.vs_call_ctx.cc_calldata /\
    abi_decode_frame d (32 + maxn * mem_sz) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `w2n (abi_decode_load CALLDATALOAD p s) * mem_sz <= maxn * mem_sz` by
    simp[LE_MULT_RCANCEL] >>
  `d + 32 < dimword (:256) /\
   w2n (abi_decode_load CALLDATALOAD p s) * mem_sz < dimword (:256)` by decide_tac >>
  drule_all calldata_bulk_accepted_sequence >> strip_tac >>
  `abi_decode_frame d (32 + maxn * mem_sz) s t` by
    (irule abi_decode_frame_widen >>
     qexistsl_tac [`d`, `32 + w2n (abi_decode_load CALLDATALOAD p s) * mem_sz`] >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  irule abi_decode_sequence_allocation_frame >>
  qexists_tac `emitted_insts st st'` >> simp[] >>
  drule_all calldata_bulk_allocation_shape >> simp[EVERY_MEM] >> metis_tac[]
QED

Theorem calldata_array_header_prefix_safe:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ d + 32 <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (cnt,c1)` >>
  rename1 `emit_void MSTORE [dst;cnt] c1 = ((),st')` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. !u. inst_mem_below_frontier i u) (emitted_insts st c1)` by
    (drule emitted_insts_emit_op >> simp[] >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
  `s1.vs_alloca_next = s.vs_alloca_next` by
    (`EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
        (emitted_insts st c1)` by
       (drule emitted_insts_emit_op >> simp[mk_inst_def,
          is_terminator_def, is_alloca_op_def]) >>
     drule_all abi_decode_sequence_allocation_frame >> simp[]) >>
  asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `s1` >> asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >> simp[]) >>
  drule emitted_insts_emit_void >> simp[] >> strip_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_mstore_prefix_safe) >>
  qexists_tac `d` >> simp[] >> metis_tac[]
QED

Theorem calldata_variable_copy_prefix_safe:
  eval_operand dst s = SOME (n2w d) /\ eval_operand size_op s = SOME (n2w sz) /\
  d < dimword (:256) /\ sz < dimword (:256) /\ d + sz <= s.vs_alloca_next ==>
  !pre i post u. [mk_inst id CALLDATACOPY [dst; src; size_op] []] =
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

Theorem calldata_bulk_payload_prefix_safe:
  abi_decode_bulk_payload dst src cnt mem_sz CALLDATALOAD (Lit 0w) st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand cnt s = SOME (n2w n) /\ fresh_vars_wrt st s /\
  d + 32 < dimword (:256) /\ n * mem_sz < dimword (:256) /\
  d + 32 + n * mem_sz <= s.vs_alloca_next ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  simp[abi_decode_bulk_payload_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] st = (sz_op,c1)` >>
  rename1 `emit_op ADD [src; Lit 32w] c1 = (src_data,c2)` >>
  rename1 `emit_op ADD [dst; Lit 32w] c2 = (dst_data,c3)` >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz)` by simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >> gvs[word_mul_n2w] >>
  `eval_operand src s1 = SOME p` by metis_tac[] >>
  `eval_operand (Lit 32w) s1 = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand dst s2 = SOME (n2w d)` by metis_tac[] >>
  `eval_operand (Lit 32w) s2 = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `run_inst_seq (emitted_insts c1 c3) s1 = OK s3 /\ inst_extends c1 c3` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st c3) s = OK s3 /\ inst_extends st c3` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  `emitted_insts st c3 = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 c3` by
    (irule EQ_TRANS >> qexists_tac `emitted_insts st c1 ++ emitted_insts c1 c3` >>
     conj_tac >- (irule emitted_insts_append >> fs[inst_extends_def]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     AP_TERM_TAC >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. !u. inst_mem_below_frontier i u) (emitted_insts st c3) /\
   EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
     (emitted_insts st c3)` by
    (asm_rewrite_tac[] >> imp_res_tac emitted_insts_emit_op >> simp[] >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def, mk_inst_def,
          is_terminator_def, is_alloca_op_def]) >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  `emitted_insts st st' = emitted_insts st c3 ++ emitted_insts c3 st'` by
    (irule emitted_insts_append >> conj_tac
     >- (qpat_x_assum `inst_extends st c3` mp_tac >> simp_tac bool_ss [inst_extends_def]) >>
     qpat_x_assum `inst_extends c3 st'` mp_tac >> simp_tac bool_ss [inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `s3` >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >> first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  drule emitted_insts_emit_void >> simp[abi_decode_copy_opcode_def] >> strip_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_variable_copy_prefix_safe) >>
  qexistsl_tac [`n*mem_sz`, `d+32`] >> simp[] >>
  gvs[word_add_n2w] >>
  `eval_operand sz_op s2 = SOME (n2w (mem_sz*n))` by metis_tac[] >>
  metis_tac[]
QED

Theorem calldata_array_header_allocation_shape:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
       fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, is_alloca_op_def]
QED

Theorem calldata_bulk_body_prefix_safe:
  abi_decode_bulk_body dst src src CALLDATALOAD (Lit 0w) mem_sz st = ((),st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d + 32 < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s) * mem_sz < dimword (:256) /\
  d + 32 + w2n (abi_decode_load CALLDATALOAD p s) * mem_sz <= s.vs_alloca_next /\
  fresh_vars_wrt st s ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  simp_tac bool_ss [abi_decode_bulk_body_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_array_header dst src CALLDATALOAD st = (cnt,c1)` >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `d < dimword (:256)` by decide_tac >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule calldata_array_header_allocation_shape >> strip_tac >>
  drule_all abi_decode_sequence_allocation_frame >> strip_tac >>
  `eval_operand src s1 = SOME p /\ eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `eval_operand cnt s1 = SOME (n2w (w2n (abi_decode_load CALLDATALOAD p s)))` by simp[] >>
  `w2n (abi_decode_load CALLDATALOAD p s) * mem_sz < dimword (:256)` by metis_tac[MULT_COMM] >>
  drule_all calldata_bulk_payload_sequence >> strip_tac >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `s1` >> conj_tac
  >- (ho_match_mp_tac (GEN_ALL calldata_array_header_prefix_safe) >>
      qexistsl_tac [`src`, `p`, `dst`, `d`, `cnt`] >> simp[] >> decide_tac) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  ho_match_mp_tac (GEN_ALL calldata_bulk_payload_prefix_safe) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[MULT_COMM]
QED

Theorem calldata_bulk_body_extends:
  abi_decode_bulk_body dst src src CALLDATALOAD (Lit 0w) mem_sz st = ((),st') ==>
  inst_extends st st'
Proof
  simp[abi_decode_bulk_body_def, abi_decode_array_header_def,
       abi_decode_bulk_payload_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  metis_tac[inst_extends_trans]
QED

Theorem calldata_bulk_prefix_safe:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME (n2w d) /\ maxn < dimword (:256) /\
  d + (32 + maxn * mem_sz) < dimword (:256) /\
  d + (32 + maxn * mem_sz) <= s.vs_alloca_next /\ fresh_vars_wrt st s ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ (Lit 0w) _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [calldata_bulk_sentinel, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn st = (count_op,c1)` >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule calldata_bulk_body_extends >> strip_tac >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  qpat_x_assum `emitted_insts st st' = _` (fn th => once_rewrite_tac[th]) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
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
      `w2n (abi_decode_load CALLDATALOAD p s) * mem_sz <= maxn * mem_sz` by
        simp[LE_MULT_RCANCEL] >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bulk_body_prefix_safe) >>
      goal_assum (drule_at Any) >> simp[] >>
      `eval_operand src t = SOME p /\ eval_operand dst t = SOME (n2w d)` by metis_tac[] >>
      `abi_decode_load CALLDATALOAD p t = abi_decode_load CALLDATALOAD p s` by
        simp[abi_decode_load_def, abi_decode_source_def] >>
      qexistsl_tac [`src`, `p`, `mem_sz`, `dst`, `d`] >> simp[] >> decide_tac) >>
  `maxn < w2n (abi_decode_load CALLDATALOAD p s)` by decide_tac >>
  drule_all calldata_count_guard_rejected_sequence >> gvs[]
QED

Theorem calldata_bulk_accepted_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ maxn < dimword (:256) /\
  d + (32 + maxn * mem_sz) < dimword (:256) /\
  d + (32 + maxn * mem_sz) <= initial.vs_alloca_next /\ fresh_vars_wrt st initial /\
  w2n (abi_decode_load CALLDATALOAD p initial) <= maxn ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= maxn /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      mem_bytes_at (d+32) (w2n (abi_decode_load CALLDATALOAD p initial) * mem_sz) t.vs_memory =
        mem_bytes_at (w2n (p+32w)) (w2n (abi_decode_load CALLDATALOAD p initial) * mem_sz)
          initial.vs_call_ctx.cc_calldata /\
      abi_decode_frame d (32 + maxn * mem_sz) initial t /\ fresh_vars_wrt st' t /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (K F)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all calldata_bulk_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bulk_prefix_safe) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[ADD_COMM]) >>
  drule_all calldata_bulk_accepted_allocation >> strip_tac >>
  qexists_tac `t` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def,
      instIdxIndepTheory.eval_op_inst_idx] >> metis_tac[]
QED

Theorem calldata_bulk_rejected_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ maxn < dimword (:256) /\
  d + (32 + maxn * mem_sz) < dimword (:256) /\
  d + (32 + maxn * mem_sz) <= initial.vs_alloca_next /\ fresh_vars_wrt st initial /\
  maxn < w2n (abi_decode_load CALLDATALOAD p initial) ==>
  frag_exec_mem ctx st st' (\s. s = initial) (K F)
    (\r. ?u. r = Abort Revert_abort u)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_bulk_shape >> strip_tac >>
  drule_all calldata_bulk_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_bulk_prefix_safe) >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[ADD_COMM]) >>
  drule_all calldata_bulk_rejected_sequence >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem calldata_bulk_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ eval_operand src initial = SOME p /\
  eval_operand dst initial = SOME (n2w d) /\ maxn < dimword (:256) /\
  d + (32 + maxn * mem_sz) < dimword (:256) /\
  d + (32 + maxn * mem_sz) <= initial.vs_alloca_next /\ fresh_vars_wrt st initial ==>
  frag_exec_mem ctx st st' (\s. s = initial)
    (\t. w2n (abi_decode_load CALLDATALOAD p initial) <= maxn /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      mem_bytes_at (d+32) (w2n (abi_decode_load CALLDATALOAD p initial) * mem_sz) t.vs_memory =
        mem_bytes_at (w2n (p+32w)) (w2n (abi_decode_load CALLDATALOAD p initial) * mem_sz)
          initial.vs_call_ctx.cc_calldata /\
      abi_decode_frame d (32 + maxn * mem_sz) initial t /\ fresh_vars_wrt st' t /\
      (!op w. eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (\r. ?u. r = Abort Revert_abort u)
Proof
  strip_tac >> Cases_on `w2n (abi_decode_load CALLDATALOAD p initial) <= maxn`
  >- (drule_all calldata_bulk_accepted_frag_mem >> strip_tac >>
      first_x_assum (qspec_then `ctx` assume_tac) >>
      irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[]) >>
  `maxn < w2n (abi_decode_load CALLDATALOAD p initial)` by decide_tac >>
  drule_all calldata_bulk_rejected_frag_mem >> strip_tac >>
  first_x_assum (qspec_then `ctx` assume_tac) >>
  irule frag_exec_mem_conseq >> goal_assum (drule_at Any) >> simp[]
QED
